import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

open Set

inductive Itv
| bot
| mk (lo hi : ℤ) (h : lo ≤ hi)

def Itv.interval (lo hi : ℤ) : Itv :=
  if h : lo ≤ hi then Itv.mk lo hi h else Itv.bot

def γ : Itv → Set ℤ
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
