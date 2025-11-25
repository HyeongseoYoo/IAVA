import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

open Set

/-- Abstract Z -/
inductive Itv
| bot
| mk (lo hi : ℤ) (h : lo ≤ hi)
deriving Repr

def Itv.interval (lo hi : ℤ) : Itv :=
  if h : lo ≤ hi then Itv.mk lo hi h else Itv.bot

def γItv : Itv → Set ℤ
| Itv.bot        => ∅
| (Itv.mk lo hi _) => {z | lo ≤ z ∧ z ≤ hi}

def add (S T : Set ℤ) : Set ℤ :=
  {z | ∃ x ∈ S, ∃ y ∈ T, z = x + y}

def add_abs (I J : Itv) : Itv :=
  match I, J with
  | Itv.bot, _ => Itv.bot
  | _, Itv.bot => Itv.bot
  | Itv.mk lo₁ hi₁ h₁, Itv.mk lo₂ hi₂ h₂ =>
      Itv.mk (lo₁ + lo₂) (hi₁ + hi₂) (by linarith)

notation I " ⊕ " J => add_abs I J

/-- Concrete locations -/
abbrev Base := ℤ
abbrev Offset := ℤ

structure Loc where
  base : Base
  offset : Offset
deriving Repr, DecidableEq

/-- Abstract locations -/
abbrev Label := Nat

structure AbsLoc where
  allocSite : Label
  offset : Itv
deriving Repr

def γLoc (env : Label → Set Base) (absℓ : AbsLoc) : Set Loc :=
  { ℓ : Loc | ℓ.base ∈ env absℓ.allocSite ∧ ℓ.offset ∈ γItv absℓ.offset }

/-- Concrete Unit -/
notation "⋅" => ()

/-- Abstract Unit -/
inductive AbsUnit where
| bot
| unit
deriving Repr, DecidableEq

def γUnit : AbsUnit → Set Unit
| AbsUnit.bot  => ∅
| AbsUnit.unit => {⋅}

/-- Concrete Value -/
inductive Value where
| int (z: ℤ)
| loc (ℓ : Loc)
| unit (u : Unit)
deriving Repr, DecidableEq

/-- Abstract Value -/
structure AbsValue where
  absint : Itv
  absloc : AbsLoc
  absunit : AbsUnit
deriving Repr

def γValue (env : Label → Set Base) (absv : AbsValue) : Set Value :=
  let intSet := {Value.int z | z ∈ γItv absv.absint}
  let locSet := {Value.loc ℓ | ℓ ∈ γLoc env absv.absloc}
  let unitSet := {Value.unit u | u ∈ γUnit absv.absunit}
  intSet ∪ locSet ∪ unitSet
