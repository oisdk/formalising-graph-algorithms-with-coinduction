{-# OPTIONS --safe #-}

module README where

-- This file contains imports for all of the proven statements in the paper.

--------------------------------------------------------------------------------
-- 1: Introduction
--------------------------------------------------------------------------------

import NeighboursGraphs using
  ( GraphOf
  ; graph
  ; module Hamiltonian
  ; pathed
  ; filtering
  ; collatz
  )

import Data.NonEmpty.Discrete using
  ( uniq
  ; covers
  )

import Data.Vert using
  ( Vert
  )


--------------------------------------------------------------------------------
-- 2: Representing Graphs
--------------------------------------------------------------------------------

import Algebra.Monus

import Data.Weighted using
  ( Weighted
  ; ⟅⟆
  ; _▹_∷_
  ; com
  ; dup
  ; trunc
  )

--------------------------------------------------------------------------------
-- 3: Algebraic Graphs
--------------------------------------------------------------------------------

import Data.Weighted.Monad using
  ( _>>=_
  ; _⋊_
  ; return
  )

import Algebra using
  ( Semiring
  ; ComMonadPlus
  ; StarSemiring
  ; WeightSemimodule
  )

import WeightedGraphs using
  ( _⊞_
  ; empty
  ; _>=>_
  ; semiringGraph
  ; _***_
  ; _+++_
  ; unit
  ; void
  ; ***-idˡ
  )

import NeighboursGraphs using
  ( pathed
  ; filtering
  )

import Codata.Neighbours using
  ( mapₙ
  )

import Data.Weighted.Free using
  ( 𝒲
  ; hom
  ; uniq
  ; 𝒲-surj
  )

--------------------------------------------------------------------------------
-- 4: Coinduction on Graphs
--------------------------------------------------------------------------------

import Data.Link
import Codata.Chain

import Codata.Pairing using
  ( Heap
  ; _⋈_
  ; merges⁺
  ; merges
  ; search
  )

import Codata.CIM using
  ( Module
  ; Ideal
  ; Equation
  ; Solution
  ; _Solves_
  ; Flat
  ; CIM -- (CIM.soln = Lemma 4.1)
  )

--------------------------------------------------------------------------------
-- 5: Quotienting Coinductive Structures
--------------------------------------------------------------------------------

import Data.Weighted.Cutoff using
  ( _⊢_
  )
  
import Algebra.Monus using
  ( WellFoundedMonus
  )

import WellFounded using
  ( Acc
  ; WellFounded
  )

import Codata.Bush using
  ( _∣_⊢_
  ; Bush
  ; Forest
  ; Equiv-UpTo
  ; search
  )

import Algebra using
  ( RightAction
  )

import Algebra.ActionCategory using
  ( Action
  ; Ob
  ; _⟶_
  ; selfAction
  )

import Algebra.MonoidActionCategory using
  ( Action
  ; Ob
  ; _⟶_
  ; selfAction
  ; Rep-iso
  )

import Codata.Neighbours using
  ( Neighbours
  ; Neighbourly
  ; searched
  ; η
  ; μ
  ; _⊪_
  ; join-prec
  ; _⋊ₙ_
  ; Heavier
  ; isearch-iso
  ; solve-disp
  )

import Codata.Neighbours.Monad

import Codata.Neighbours.Solves using
  ( solution-disp
  ; cim
  ; _∗
  )

--------------------------------------------------------------------------------
-- 6: Case studies
--------------------------------------------------------------------------------

import TopoSort using
  ( topo-sort
  )

import Data.Set.Noetherian using
  ( NoethAcc
  )

import NeighboursGraphs using
  ( dijkstra
  )
