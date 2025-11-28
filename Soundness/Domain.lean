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

/-- Concrete locations -/
abbrev Base := ℤ
abbrev Offset := ℤ

structure Loc where
  base : Base
  offset : Offset
deriving Repr, DecidableEq

/-- Abstract locations -/
abbrev ℙ := Nat

inductive AbsLoc where
| bot
| mk (allocSite : ℙ) (offset : Itv)
deriving Repr

def γLoc (env : ℙ → Set Base) (absℓ : AbsLoc) : Set Loc :=
match absℓ with
| AbsLoc.bot => ∅
| AbsLoc.mk allocSite offset => { ℓ : Loc | ℓ.base ∈ env allocSite ∧ ℓ.offset ∈ γItv offset }

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

def γValue (penv : ℙ → Set Base) (absv : AbsValue) : Set Value :=
  let intSet := {Value.int z | z ∈ γItv absv.absint}
  let locSet := {Value.loc ℓ | ℓ ∈ γLoc penv absv.absloc}
  let unitSet := {Value.unit u | u ∈ γUnit absv.absunit}
  intSet ∪ locSet ∪ unitSet

/-- Semantic operators -/

def add (S T : Set ℤ) : Set ℤ :=
  {z | ∃ x ∈ S, ∃ y ∈ T, z = x + y}

def addVal (S T : Set Value) : Set Value :=
  { v | ∃ z1 z2,
      v = Value.int (z1 + z2)
      ∧ Value.int z1 ∈ S
      ∧ Value.int z2 ∈ T }

def addAbs_itv (I J : Itv) : Itv :=
  match I, J with
  | Itv.bot, _ => Itv.bot
  | _, Itv.bot => Itv.bot
  | Itv.mk lo₁ hi₁ h₁, Itv.mk lo₂ hi₂ h₂ =>
      Itv.mk (lo₁ + lo₂) (hi₁ + hi₂) (by linarith)

notation I " ⊕ " J => addAbs_itv I J

def addAbs (v1 v2 : AbsValue) : AbsValue :=
  let absint :=
    match v1.absint, v2.absint with
    | I, J => I ⊕ J
  AbsValue.mk absint AbsLoc.bot AbsUnit.bot

-- def equal : Value → Value → Prop
-- | Value.int z1, Value.int z2 => z1 = z2
-- | Value.loc ℓ1, Value.loc ℓ2 => ℓ1 = ℓ2
-- | Value.unit _, Value.unit _ => True
-- | _, _ => False

-- def eqAbs (v1 v2: AbsValue) : Prop :=
--   let int_eq := match v1.absint, v2.absint with
--                  | Itv.bot, _ => False
--                  | _, Itv.bot => False
--                  | Itv.mk lo₁ hi₁ h₁, Itv.mk lo₂ hi₂ h₂ =>
--                      lo₁ = lo₂ ∧ hi₁ = hi₂
--   let loc_eq := if v1.absloc = AbsLoc.bot ∨ v2.absloc = AbsLoc.bot then False
--                  else v1.absloc = v2.absloc
--   let unit_eq := if v1.absunit = AbsUnit.bot ∨ v2.absunit = AbsUnit.bot then False
--                  else v1.absunit = v2.absunit
