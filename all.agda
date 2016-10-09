-- this is effectively a CM make file. it just includes all the files that
-- exist in the directory in the right order so that one can check that
-- everything compiles cleanly and has no unfilled holes

-- data structures
open import List
open import Nat
open import Prelude

-- basic stuff: core definitions, etc
open import core
open import checks
open import judgemental-erase
open import judgemental-inconsistency
open import moveerase
open import examples
open import structural

-- first wave theorems
open import sensibility
open import aasubsume-min
open import determinism

-- second wave theorems (checksums)
open import reachability
open import constructability
