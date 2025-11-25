import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Soundness.Domain

open Set

lemma add_abs_sound_γ (I J : Itv) :
  add (γ I) (γ J) ⊆ γ (I ⊕ J) := by
  intro z hz
  unfold add at hz
  cases I with
  | bot =>
      cases J with
      | bot =>
          simp [γ] at hz
      | mk lo₂ hi₂ h₂ =>
          simp [γ] at hz
  | mk lo₁ hi₁ h₁ =>
      cases J with
      | bot =>
          simp [γ] at hz
      | mk lo₂ hi₂ h₂ =>
          rcases hz with ⟨x, hx, y, hy, rfl⟩
          rcases hx with ⟨hx_lo, hx_hi⟩
          rcases hy with ⟨hy_lo, hy_hi⟩
          simp [γ, add_abs]
          constructor
          · linarith
          · linarith
