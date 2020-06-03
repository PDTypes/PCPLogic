module run where

open import satellite
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Data.List hiding (_++_)
open import Data.String

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

showC : C -> String
showC satellite0 = "satellite0 "
showC instrument0 = "instrument0 "
showC image1 = "image1 "
showC spectrograph2 = "spectrograph2 "
showC thermograph0 = "thermograph0 "
showC star0 = "star0 "
showC groundstation1 = "groundstation1 "
showC groundstation2 = "groundstation2 "
showC phenomenon3 = "phenomenon3 "
showC phenomenon4 = "phenomenon4 "
showC star5 = "star5 "
showC phenomenon6 = "phenomenon6 "

showR : R -> String
showR (mode x) = "mode " ++ showC x
showR (instrument x) = "instrument " ++ showC x
showR (direction x) = "direction " ++ showC x
showR (satellite x) = "satellite " ++ showC x
showR (calibration_target i d) = "calibration_target " ++ showC i ++ showC d
showR (have_image d m) = "have_image " ++ showC d ++ showC m
showR (calibrated i) = "calibrated " ++ showC i
showR (power_on i) = "power_on " ++ showC i
showR (power_avail s) = "power_avail " ++ showC s
showR (pointing s d) = "pointing " ++ showC s ++ showC d
showR (supports i m) = "supports " ++ showC i ++ showC m
showR (on_board i s) = "on_board " ++ showC i ++ showC s

showEval : List R -> String
showEval [] = "emp"
showEval (x ∷ xs) = showR x ++ " * " ++ (showEval xs)

main : IO ⊤
main = putStrLn (showEval world-eval)
