import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Soundness.Domain

open Set

lemma γValue_int_iff (env : ℙ → Set Base) (a : AbsValue) (z : ℤ) :
    Value.int z ∈ γValue env a ↔ z ∈ γItv a.absint := by
    simp [γValue]

lemma add_itv_sound (I J : Itv) :
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
          simp [γItv, addAbs_itv]
          constructor
          · linarith
          · linarith

lemma add_itv_of_val_sound (a1 a2 : AbsValue) :
    add (γItv a1.absint) (γItv a2.absint) ⊆ γItv (addAbs a1 a2).absint := by
    intro z hz
    -- (addAbs a1 a2).absint = a1.absint ⊕ a2.absint 임을 이용
    have : z ∈ γItv (a1.absint ⊕ a2.absint) := add_itv_sound a1.absint a2.absint hz
    simpa [addAbs] using this

lemma add_sound (env : ℙ → Set Base) (a1 a2 : AbsValue) :
addVal (γValue env a1) (γValue env a2) ⊆ γValue env (addAbs a1 a2) := by
  intro v hv
  rcases hv with ⟨z1, z2, rfl, hz1, hz2⟩

  -- 1단계: γValue_int_iff 의 left-to-right 방향 사용
  have hz1' : z1 ∈ γItv a1.absint :=
    (γValue_int_iff env a1 z1).1 hz1
  have hz2' : z2 ∈ γItv a2.absint :=
    (γValue_int_iff env a2 z2).1 hz2

  -- 2단계: z1+z2가 add(γItv a1.absint, γItv a2.absint)에 포함됨
  have hSum : (z1 + z2) ∈ add (γItv a1.absint) (γItv a2.absint) := by
    refine ⟨z1, ?_, z2, ?_, rfl⟩
    · exact hz1'
    · exact hz2'

  -- 3단계: itv soundness를 이용해 abstract interval에 포함시킨다.
  have hInItv : (z1 + z2) ∈ γItv (addAbs a1 a2).absint :=
    add_itv_of_val_sound a1 a2 hSum

  -- 4단계: γValue_int_iff 의 right-to-left 방향 사용
  exact (γValue_int_iff env (addAbs a1 a2) (z1 + z2)).2 hInItv
