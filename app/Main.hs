module Main where

import Control.Monad (forM_)
import Data.ByteString.Lazy qualified as BL
import Data.Map as Map
import Data.Word
import Instructions
import LLVM.Core (CodeGenModule, Function, IsConst (constOf), Linkage (PrivateLinkage), createGlobal)
import Tracing

newtype TraceFunction = TraceFunction {funcStart :: Address}

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

mainFunc :: CodeGenModule (Function (IO ()))
mainFunc = do
  let createRegister i = do
        globalVar <- createGlobal True PrivateLinkage (constOf (0 :: Word8))
        pure (i, globalVar)
  registers <- Map.fromList <$> mapM createRegister [0 .. (registersCount - 1)]
  let createFunction instructions = do
        undefined
  undefined

main :: IO ()
main = do
  res <- disasmToFunctions "tetris.ch8"
  case res of
    Left str -> error str
    Right (TraceResult {instructions = instructions, functions = functions}) ->
      forM_ (Map.assocs instructions) $ \(addr, InstructionData {iInstruction = inst}) -> do
        let TraceFunction {funcStart = func} =
              functions ! addr
        putStrLn $ "(" ++ show func ++ ") " ++ show addr ++ ":\t" ++ show inst
