import Mathlib

open Quaternion

noncomputable def omega : ℍ where
  re := 2⁻¹
  imI := 2⁻¹
  imJ := 2⁻¹
  imK := 2⁻¹

def Hurwitz : Type :=
  (Subring.closure {1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩} : Subring ℍ)

namespace Hurwitz

@[coe]
def coe (q : Hurwitz) : ℍ := q.1

instance : Coe Hurwitz ℍ := ⟨coe⟩

@[simp]
lemma coe_mk (q : ℍ) (hq : q ∈ Subring.closure _) : coe ⟨q, hq⟩ = q := rfl

lemma aux (q : Hurwitz) :
    ∃ a b c d : ℤ, (q : ℍ) = ⟨a, b, c, d⟩ ∨ (q : ℍ) = ⟨a + 2⁻¹, b + 2⁻¹, c + 2⁻¹, d + 2⁻¹⟩ := by
  obtain ⟨x, hx⟩ := q
  refine Subring.closure_induction hx ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl hx =>
      use 1, 0, 0, 0
      left
      simp [hx]
      rfl
    | inr hx =>
    cases hx with
    | inl hx =>
      use 0, 1, 0, 0
      left
      simp [hx]
    | inr hx =>
    cases hx with
    | inl hx =>
      use 0, 0, 1, 0
      left
      simp [hx]
    | inr hx =>
      use 0, 0, 0, 0
      right
      simp [hx]
  · use  0, 0, 0, 0
    left
    simp [hx]
    rfl
  · use 1, 0, 0, 0
    left
    simp [hx]
    rfl
  · rintro x y ⟨x1, x2, x3, x4, hx|hx⟩ ⟨y1, y2, y3, y4, hy|hy⟩
    · use (x1 + y1), (x2 + y2), (x3 + y3), (x4 + y4)
      left
      simp [Quaternion.ext_iff] at *
      sorry


    done
  done

end Hurwitz
