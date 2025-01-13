module Main where

import Control.Monad (forM, forM_, void)
import Data.ByteString.Lazy qualified as BL
import Data.List as List
import Data.List.NonEmpty as NEList
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (swap)
import Data.Word
import GHC.Stack (HasCallStack)
import Instructions
import LLVM.Core (CmpPredicate (CmpEQ, CmpNE), CodeGenModule, Function, Global, IsConst (constOf), Linkage (PrivateLinkage), add, and, br, cmp, condBr, createBasicBlock, createFunction, createGlobal, defineBasicBlock, defineModule, ext, load, newModule, or, ret, shl, shr, store, sub, valueOf, writeBitcodeToFile, xor)
import Tracing

newtype TraceFunction = TraceFunction {funcStart :: Address} deriving (Eq, Ord)

data InstructionData = InstructionData
  { iInstruction :: !Instruction,
    iNextAddresses :: ![Address]
  }

data TraceResult = TraceResult
  { instructions :: !(Map Address InstructionData),
    functions :: !(Map Address TraceFunction)
  }

disasmToFunctions :: String -> IO (Either String TraceResult)
disasmToFunctions filename = do
  bl <- BL.readFile filename
  let callback
        TraceResult
          { instructions = curInstructions,
            functions = curFunctions
          }
        TraceContext
          { current =
              TraceInstruction
                { address = addr,
                  instruction = inst
                },
            previous = prevInst,
            next = nextAddrs
          } =
          let newInstructions =
                Map.insert addr (InstructionData inst nextAddrs) curInstructions
              addNewFunction =
                Map.insert addr (TraceFunction addr) curFunctions
              newFunctions = case prevInst of
                Nothing ->
                  addNewFunction
                Just (TraceInstruction {address = prevAddr, instruction = prevInstruction}) ->
                  let curFunction =
                        curFunctions ! prevAddr
                      addToCurFunction =
                        Map.insert addr curFunction curFunctions
                   in case prevInstruction of
                        InstCall callAddr ->
                          if callAddr == addr
                            then addNewFunction
                            else addToCurFunction
                        _ ->
                          addToCurFunction
           in TraceResult newInstructions newFunctions
  pure (trace bl callback (TraceResult Map.empty Map.empty))

registersCount :: Int
registersCount = 16

genFunction :: (HasCallStack) => Global Word16 -> Map Int (Global Word8) -> Map Address InstructionData -> Map Address (NonEmpty Address) -> Address -> CodeGenModule (Function (IO ()))
genFunction iGlobal registers instructions functionInstructions funcStart = do
  let curFuncInstructions =
        functionInstructions Map.! funcStart
      extractLabels instrs = do
        InstructionData {iInstruction = instr, iNextAddresses = nextAddrs} <- instrs
        case nextAddrs of
          a@[_, _] ->
            case instr of
              InstCall _ ->
                []
              _ ->
                a
          [_] ->
            case instr of
              InstJump jumpAddr ->
                [jumpAddr]
              InstJumpI _ ->
                error "Do not support JUMPI yet"
              _ -> []
          _ -> []
      labelAddresses =
        extractLabels $ NEList.toList $ NEList.map (instructions Map.!) curFuncInstructions
      labelAddressesSet =
        Set.fromList labelAddresses
  createFunction PrivateLinkage $ do
    blocks <-
      Map.fromList
        <$> forM
          labelAddresses
          ( \addr -> do
              block <- createBasicBlock
              pure (addr, block)
          )
    let loop curAddr = do
          let InstructionData {iInstruction = instr, iNextAddresses = nextAddrs} =
                instructions Map.! curAddr
          case nextAddrs of
            [a1, a2] ->
              case instr of
                InstSke iReg w8 -> do
                  let reg =
                        getR iReg
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  regV <- load reg
                  test <- cmp CmpEQ regV (constOf w8)
                  condBr test b2 b1
                InstSkne iReg w8 -> do
                  let reg =
                        getR iReg
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  regV <- load reg
                  test <- cmp CmpNE regV (constOf w8)
                  condBr test b2 b1
                InstSkre iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  test <- cmp CmpEQ reg1V reg2V
                  condBr test b2 b1
                InstSkrne iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  test <- cmp CmpNE reg1V reg2V
                  condBr test b2 b1
                InstSkpr iReg -> do
                  let reg =
                        getR iReg
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  -- TODO implement
                  br b1
                InstSkup iReg -> do
                  let reg =
                        getR iReg
                      b1 =
                        getB a1
                      b2 =
                        getB a2
                  -- TODO implement
                  br b2
                InstCall _ ->
                  -- TODO: implement CALL
                  loop a2
                invalidInstr -> error ("Invalid instruction: " ++ show invalidInstr)
            [] ->
              case instr of
                InstRts ->
                  ret ()
                invalidInstr -> error ("Invalid instruction: " ++ show invalidInstr)
            [a1] ->
              case instr of
                InstJump jumpAddr -> do
                  let block =
                        blocks Map.! jumpAddr
                  br block
                  pure ()
                InstSys _ ->
                  loop a1
                InstClr ->
                  -- TODO: implement CLR
                  loop a1
                InstLoad iReg w8 -> do
                  let reg =
                        getR iReg
                  store (valueOf w8) reg
                  loop a1
                InstAdd iReg w8 -> do
                  let reg =
                        getR iReg
                  regV <- load reg
                  res <- add regV (valueOf w8)
                  store res reg
                  loop a1
                InstMove iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg2V <- load reg2
                  store reg2V reg1
                  loop a1
                InstOr iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- LLVM.Core.or reg1V reg2V
                  store res reg1
                  loop a1
                InstAnd iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- LLVM.Core.and reg1V reg2V
                  store res reg1
                  loop a1
                InstXor iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- LLVM.Core.xor reg1V reg2V
                  store res reg1
                  loop a1
                InstAddr iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- add reg1V reg2V
                  store res reg1
                  loop a1
                InstSub iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- sub reg1V reg2V
                  store res reg1
                  loop a1
                InstShr iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- shr reg1V reg2V
                  store res reg1
                  loop a1
                InstShl iReg1 iReg2 -> do
                  let reg1 =
                        getR iReg1
                      reg2 =
                        getR iReg2
                  reg1V <- load reg1
                  reg2V <- load reg2
                  res <- shl reg1V reg2V
                  store res reg1
                  loop a1
                InstLoadI (Address w16) -> do
                  store (valueOf w16) iGlobal
                  loop a1
                InstDraw iReg1 iReg2 w8 -> do
                  -- TODO implement DRAW
                  loop a1
                InstRand iReg w8 -> do
                  -- TODO implement RAND
                  loop a1
                InstLoadD iReg -> do
                  -- TODO implement LOADD
                  loop a1
                InstAddI iReg -> do
                  let reg =
                        getR iReg
                  iv <- load iGlobal
                  regV <- load reg
                  regV16 <- ext regV
                  res <- add iv regV16
                  store res iGlobal
                  loop a1
                InstMoveD iReg -> do
                  let reg =
                        getR iReg
                  store (valueOf (0 :: Word8)) reg
                  loop a1
                InstStor iReg -> do
                  let reg =
                        getR iReg
                  -- TODO implement STOR
                  loop a1
                InstBcd iReg -> do
                  -- TODO implement BCD
                  loop a1
                InstRead iReg -> do
                  -- TODO implement READ
                  loop a1
                InstLdspr iReg -> do
                  -- TODO implement LDSPR
                  loop a1
                invalidInstr -> error ("Instruction is not supported yet: " ++ show invalidInstr)
            _ -> error "Invalid nextAddresses"
        getR (Register w8) =
          registers Map.! (fromIntegral w8)
        getB addr =
          blocks Map.! addr
    void $ loop funcStart
    forM_ labelAddresses $ \addr -> do
      let block =
            blocks Map.! addr
      defineBasicBlock block
      loop addr

mainFunc :: (HasCallStack) => Map Address InstructionData -> Map Address TraceFunction -> CodeGenModule (Function (IO ()))
mainFunc instructions functions = do
  let createRegister i = do
        globalVar <- createGlobal True PrivateLinkage (constOf (0 :: Word8))
        pure (i, globalVar)
  registers <- Map.fromList <$> mapM createRegister [0 .. (registersCount - 1)]
  iGlobal <- createGlobal True PrivateLinkage (constOf (0 :: Word16))
  let functionInstructions =
        Map.fromList $ List.map toMapPair $ NEList.groupBy onFst $ List.sortOn fst $ List.map swap $ Map.toList functions
      onFst x y =
        fst x == fst y
      toMapPair l =
        (unwrapFunc (fst (NEList.head l)), NEList.sort (NEList.map snd l))
      unwrapFunc (TraceFunction addr) =
        addr
  generatedFunctions <-
    Map.fromList
      <$> forM
        (Map.keys functionInstructions)
        ( \addr -> do
            func <- genFunction iGlobal registers instructions functionInstructions addr
            pure (addr, func)
        )
  pure $ generatedFunctions Map.! startAddress

main :: IO ()
main = do
  res <- disasmToFunctions "tetris.ch8"
  case res of
    Left str -> error str
    Right (TraceResult {instructions = instructions, functions = functions}) -> do
      forM_ (Map.assocs instructions) $ \(addr, InstructionData {iInstruction = inst}) -> do
        let TraceFunction {funcStart = func} =
              functions ! addr
        putStrLn $ "(" ++ show func ++ ") " ++ show addr ++ ":\t" ++ show inst
      mainModule <- newModule
      void $ defineModule mainModule $ mainFunc instructions functions
      writeBitcodeToFile "program.bitcode" mainModule
