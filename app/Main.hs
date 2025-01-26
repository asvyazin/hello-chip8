{-# LANGUAGE ForeignFunctionInterface #-}

module Main where

import Control.Monad (forM, forM_, void)
import Control.Monad.Random.Class (MonadRandom (getRandom))
import Data.ByteString.Lazy qualified as BL
import Data.List as List
import Data.List.NonEmpty as NEList
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (swap)
import Data.Word
import Foreign.Ptr
import GHC.Stack (HasCallStack)
import Instructions
import LLVM.Core
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

keyIsPressed :: Word8 -> IO Bool
keyIsPressed _ = pure False

foreign import ccall "wrapper"
  wrapKeyIsPressed :: (Word8 -> IO Bool) -> IO (FunPtr (Word8 -> IO Bool))

draw :: Word16 -> Word8 -> Word8 -> Word8 -> IO ()
draw spriteAddr screenX screenY spriteBytes =
  pure () -- TODO

foreign import ccall "wrapper"
  wrapDraw :: (Word16 -> Word8 -> Word8 -> Word8 -> IO ()) -> IO (FunPtr (Word16 -> Word8 -> Word8 -> Word8 -> IO ()))

randomW8 :: IO Word8
randomW8 = getRandom

foreign import ccall "wrapper"
  wrapRandomW8 :: IO Word8 -> IO (FunPtr (IO Word8))

setWord8 :: Word16 -> Word8 -> IO ()
setWord8 addr w8 = pure () -- TODO

foreign import ccall "wrapper"
  wrapSetWord8 :: (Word16 -> Word8 -> IO ()) -> IO (FunPtr (Word16 -> Word8 -> IO ()))

getWord8 :: Word16 -> IO Word8
getWord8 addr = pure 0 -- TODO

foreign import ccall "wrapper"
  wrapGetWord8 :: (Word16 -> IO Word8) -> IO (FunPtr (Word16 -> IO Word8))

genFunction ::
  (HasCallStack) =>
  Global Word16 ->
  FunPtr (Word8 -> IO Bool) ->
  FunPtr (Word16 -> Word8 -> Word8 -> Word8 -> IO ()) ->
  FunPtr (IO Word8) ->
  FunPtr (Word16 -> Word8 -> IO ()) ->
  FunPtr (Word16 -> IO Word8) ->
  Map Address (Function (IO ())) ->
  Map Int (Global Word8) ->
  Map Address InstructionData ->
  Map Address (NonEmpty Address) ->
  Address ->
  Function (IO ()) ->
  CodeGenModule ()
genFunction
  iGlobal
  wrapped_keyIsPressed
  wrapped_draw
  wrapped_randomW8
  wrapped_setWord8
  wrapped_getWord8
  allFunctions
  registers
  instructions
  functionInstructions
  funcStart
  curFunction = do
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
        labelAddressesUnique =
          Set.toList labelAddressesSet
    defineFunction curFunction $ do
      blocks <-
        Map.fromList
          <$> forM
            labelAddressesUnique
            ( \addr -> do
                block <- newNamedBasicBlock $ "L" ++ show addr
                pure (addr, block)
            )
      let loop curAddr = do
            let gotoNext a =
                  if Set.member a labelAddressesSet
                    then br (blocks Map.! a)
                    else loop a
                InstructionData {iInstruction = instr, iNextAddresses = nextAddrs} =
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
                    regV <- load reg
                    native_keyIsPressed <- staticFunction wrapped_keyIsPressed
                    test <- call native_keyIsPressed regV
                    condBr test b2 b1
                  InstSkup iReg -> do
                    let reg =
                          getR iReg
                        b1 =
                          getB a1
                        b2 =
                          getB a2
                    regV <- load reg
                    native_keyIsPressed <- staticFunction wrapped_keyIsPressed
                    test <- call native_keyIsPressed regV
                    condBr test b1 b2
                  InstCall aCall -> do
                    let func =
                          allFunctions Map.! aCall
                    void $ call func
                    gotoNext a2
                  invalidInstr -> error ("Invalid instruction: " ++ show invalidInstr)
              [] ->
                case instr of
                  InstRts ->
                    ret ()
                  invalidInstr -> error ("Invalid instruction: " ++ show invalidInstr)
              [a1] -> do
                case instr of
                  InstJump jumpAddr -> do
                    let block =
                          blocks Map.! jumpAddr
                    br block
                    pure ()
                  InstSys _ ->
                    gotoNext a1
                  InstClr ->
                    -- TODO: implement CLR
                    gotoNext a1
                  InstLoad iReg w8 -> do
                    let reg =
                          getR iReg
                    store (valueOf w8) reg
                    gotoNext a1
                  InstAdd iReg w8 -> do
                    let reg =
                          getR iReg
                    regV <- load reg
                    res <- add regV (valueOf w8)
                    store res reg
                    gotoNext a1
                  InstMove iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg2V <- load reg2
                    store reg2V reg1
                    gotoNext a1
                  InstOr iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- LLVM.Core.or reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstAnd iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- LLVM.Core.and reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstXor iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- LLVM.Core.xor reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstAddr iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- add reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstSub iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- sub reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstShr iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- shr reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstShl iReg1 iReg2 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    res <- shl reg1V reg2V
                    store res reg1
                    gotoNext a1
                  InstLoadI (Address w16) -> do
                    store (valueOf w16) iGlobal
                    gotoNext a1
                  InstDraw iReg1 iReg2 w8 -> do
                    let reg1 =
                          getR iReg1
                        reg2 =
                          getR iReg2
                    reg1V <- load reg1
                    reg2V <- load reg2
                    iValue <- load iGlobal
                    native_draw <- staticFunction wrapped_draw
                    void $ call native_draw iValue reg1V reg2V (valueOf w8)
                    gotoNext a1
                  InstRand iReg w8 -> do
                    native_randomW8 <- staticFunction wrapped_randomW8
                    let reg =
                          getR iReg
                    rndW8 <- call native_randomW8
                    resW8 <- LLVM.Core.and rndW8 (valueOf w8)
                    store resW8 reg
                    gotoNext a1
                  InstLoadD iReg -> do
                    -- TODO implement LOADD
                    gotoNext a1
                  InstAddI iReg -> do
                    let reg =
                          getR iReg
                    iv <- load iGlobal
                    regV <- load reg
                    regV16 <- ext regV
                    res <- add iv regV16
                    store res iGlobal
                    gotoNext a1
                  InstMoveD iReg -> do
                    let reg =
                          getR iReg
                    store (valueOf (0 :: Word8)) reg
                    gotoNext a1
                  InstStor (Register iReg) -> do
                    native_setWord8 <- staticFunction wrapped_setWord8
                    iv <- load iGlobal
                    let storLoop curAddrV curReg
                          | curReg == iReg =
                              storReg curAddrV curReg
                          | otherwise = do
                              storReg curAddrV curReg
                              newAddrV <- add curAddrV (valueOf 2)
                              storLoop newAddrV (curReg + 1)
                        storReg addrV curReg = do
                          let reg =
                                getR (Register curReg)
                          v <- load reg
                          void $ call native_setWord8 addrV v
                    storLoop iv (0 :: Word8)
                    gotoNext a1
                  InstBcd iReg -> do
                    -- TODO implement BCD
                    gotoNext a1
                  InstRead (Register iReg) -> do
                    native_getWord8 <- staticFunction wrapped_getWord8
                    iv <- load iGlobal
                    let readLoop curAddrV curReg
                          | curReg == iReg =
                              readReg curAddrV curReg
                          | otherwise = do
                              readReg curAddrV curReg
                              newAddrV <- add curAddrV (valueOf 2)
                              readLoop newAddrV (curReg + 1)
                        readReg addrV curReg = do
                          let reg =
                                getR (Register curReg)
                          v <- call native_getWord8 addrV
                          store v reg
                    readLoop iv (0 :: Word8)
                    gotoNext a1
                  InstLdspr iReg -> do
                    -- TODO implement LDSPR
                    gotoNext a1
                  invalidInstr -> error ("Instruction is not supported yet: " ++ show invalidInstr)
              _ -> error "Invalid nextAddresses"
          getR (Register w8) =
            registers Map.! fromIntegral w8
          getB addr =
            blocks Map.! addr
      void $ loop funcStart
      forM_ labelAddressesUnique $ \addr -> do
        let block =
              blocks Map.! addr
        defineBasicBlock block
        loop addr

mainFunc ::
  (HasCallStack) =>
  FunPtr (Word8 -> IO Bool) ->
  FunPtr (Word16 -> Word8 -> Word8 -> Word8 -> IO ()) ->
  FunPtr (IO Word8) ->
  FunPtr (Word16 -> Word8 -> IO ()) ->
  FunPtr (Word16 -> IO Word8) ->
  Map Address InstructionData ->
  Map Address TraceFunction ->
  CodeGenModule (Function (IO ()))
mainFunc
  wrapped_keyIsPressed
  wrapped_draw
  wrapped_randomW8
  wrapped_setWord8
  wrapped_getWord8
  instructions
  functions = do
    setTarget "x86_64"
    setDataLayout "e"
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
    let functionStarts =
          Map.keys functionInstructions
    allFunctions <-
      Map.fromList
        <$> forM
          functionStarts
          ( \addr -> do
              let linkage =
                    if addr == startAddress then ExternalLinkage else PrivateLinkage
              func <- newNamedFunction linkage $ "func_" ++ show addr
              pure (addr, func)
          )
    forM_
      functionStarts
      ( \addr -> do
          let curFunction =
                allFunctions Map.! addr
          genFunction iGlobal wrapped_keyIsPressed wrapped_draw wrapped_randomW8 wrapped_setWord8 wrapped_getWord8 allFunctions registers instructions functionInstructions addr curFunction
      )
    pure $ allFunctions Map.! startAddress

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
      wrapped_keyIsPressed <- wrapKeyIsPressed keyIsPressed
      wrapped_draw <- wrapDraw draw
      wrapped_randomW8 <- wrapRandomW8 randomW8
      wrapped_setWord8 <- wrapSetWord8 setWord8
      wrapped_getWord8 <- wrapGetWord8 getWord8
      mainModule <- newModule
      void $ defineModule mainModule $ mainFunc wrapped_keyIsPressed wrapped_draw wrapped_randomW8 wrapped_setWord8 wrapped_getWord8 instructions functions
      -- optimizeRes <- optimizeModule 2 mainModule
      -- putStrLn $ "Optimize result: " ++ show optimizeRes
      writeBitcodeToFile "program.bitcode" mainModule
      -- TODO run module
      freeHaskellFunPtr wrapped_getWord8
      freeHaskellFunPtr wrapped_setWord8
      freeHaskellFunPtr wrapped_randomW8
      freeHaskellFunPtr wrapped_draw
      freeHaskellFunPtr wrapped_keyIsPressed
