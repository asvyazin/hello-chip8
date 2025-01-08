module Tracing where

import Control.Monad.Error.Class (MonadError (throwError))
import Control.Monad.State (MonadState (get, put), runStateT)
import Data.Binary.Get (runGet)
import Data.ByteString.Lazy as BL
import Data.List qualified as L
import Data.Sequence as Seq
import Data.Set as Set
import Data.Word
import Instructions

newtype TraceState
  = TraceState {traceI :: Maybe Address}

data TraceInstruction = TraceInstruction
  { address :: !Address,
    instruction :: !Instruction
  }

data TraceContext = TraceContext
  { current :: !TraceInstruction,
    previous :: !(Maybe TraceInstruction),
    next :: ![Address]
  }

data TraceAddressToProcess = TraceAddressToProcess
  { previousAddress :: !(Maybe Address),
    traceState :: !TraceState,
    currentAddress :: !Address
  }

startAddress :: Address
startAddress = Address 0x200

trace :: BL.ByteString -> (s -> TraceContext -> s) -> s -> Either String s
trace program callback s0 =
  traceIter s0 (Seq.singleton (TraceAddressToProcess Nothing (TraceState Nothing) startAddress)) Set.empty
  where
    traceIter curS Seq.Empty _ =
      pure curS
    traceIter curS (TraceAddressToProcess {previousAddress = prevX, currentAddress = x, traceState = curState} :<| xs) processedAddresses = do
      let curInst =
            getInstByAddr x
          prevTraceInst = do
            prevAddr <- prevX
            pure $ TraceInstruction prevAddr $ getInstByAddr prevAddr
          nextProcessedAddresses =
            Set.insert x processedAddresses
      (additionalAddresses, nextState) <- runStateT (nextAddresses x curInst) curState
      let nextS =
            callback curS (TraceContext (TraceInstruction x curInst) prevTraceInst additionalAddresses)
          nextAddressesToProcess =
            Seq.fromList (L.map (TraceAddressToProcess (Just x) nextState) (L.filter (`Set.notMember` processedAddresses) additionalAddresses)) >< xs
      traceIter nextS nextAddressesToProcess nextProcessedAddresses
    getInstByAddr (Address addr) =
      let bl =
            BL.drop (fromIntegral (addr - startAddrValue)) program
          (Address startAddrValue) = startAddress
       in runGet parseInstruction bl

instSize :: Word16
instSize = 2

nextInstAddr :: Address -> Address
nextInstAddr (Address curAddr) =
  Address (curAddr + instSize)

nextAddresses :: (MonadState TraceState m, MonadError String m) => Address -> Instruction -> m [Address]
nextAddresses _ InstRts =
  pure []
nextAddresses _ (InstJump jumpAddr) =
  pure [jumpAddr]
nextAddresses curAddr (InstCall callAddr) =
  pure [callAddr, nextInstAddr curAddr]
nextAddresses curAddr (InstSke _ _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstSkne _ _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstSkre _ _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstSkrne _ _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstSkpr _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstSkup _) =
  pure [nextAddr, nextInstAddr nextAddr]
  where
    nextAddr = nextInstAddr curAddr
nextAddresses curAddr (InstLoadI addr) = do
  put (TraceState (Just addr))
  pure [nextInstAddr curAddr]
nextAddresses _ (InstJumpI (Address addr)) = do
  TraceState {traceI = maybeAddr0} <- get
  case maybeAddr0 of
    Nothing -> throwError "JUMPI without previous LOADI"
    Just (Address addr0) ->
      pure [Address (addr0 + addr)]
nextAddresses curAddr _ =
  pure [nextInstAddr curAddr]
