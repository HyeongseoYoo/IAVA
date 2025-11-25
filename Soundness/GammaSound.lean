import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Soundness.Domain

open Set

lemma add_abs_sound_γ (I J : Itv) :
  add (γItv I) (γItv J) ⊆ γItv (I ⊕ J) := by
  intro z hz
  unfold add at hz
  cases I with
  | bot =>
      cases J with
      | bot =>
          simp [γItv] at hz
      | mk lo₂ hi₂ h₂ =>
          simp [γItv] at hz
  | mk lo₁ hi₁ h₁ =>
      cases J with
      | bot =>
          simp [γItv] at hz
      | mk lo₂ hi₂ h₂ =>
          rcases hz with ⟨x, hx, y, hy, rfl⟩
          rcases hx with ⟨hx_lo, hx_hi⟩
          rcases hy with ⟨hy_lo, hy_hi⟩
          simp [γItv, add_abs]
          constructor
          · linarith
          · linarith
