import Mathlib.Data.PNat.Prime
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Tactic.Peel
/-

# Example of a space of automorphic forms

-/

/-- We define the profinite completion of ℤ explicitly as compatible elements of ℤ/Nℤ for
all positive integers `N`. We declare it as a subring of `∏_{N ≥ 1} (ℤ/Nℤ)`, and then promote it
to a type. -/
def ZHat : Type := {
  carrier := { f : Π M : ℕ+, ZMod M | ∀ (D N : ℕ+) (h : (D : ℕ) ∣ N),
    ZMod.castHom h (ZMod D) (f N) = f D },
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.neg_apply] at *
    peel hx with D N hD hx
    rw [ZMod.cast_neg hD, hx]
  add_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.add_apply] at *
    intro D N hD
    rw [ZMod.cast_add hD, ha _ _ hD, hb _ _ hD]
  one_mem' := by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.one_apply]
    intro D N hD
    rw [ZMod.cast_one hD]
  mul_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.mul_apply] at *
    intro D N hD
    rw [ZMod.cast_mul hD, ha _ _ hD, hb _ _ hD]
  : Subring (Π n : ℕ+, ZMod n)}
deriving CommRing

namespace ZHat

instance : DFunLike ZHat ℕ+ (fun (N : ℕ+) ↦ ZMod N) where
  coe z := z.1
  coe_injective' M N := by simp_all

-- Try to avoid introducing `z.1` and `z.2`.
-- @[simp]
-- lemma val_apply (z : ZHat) (n : ℕ+) : z.1 n = z n := rfl

lemma prop (z : ZHat) (D N : ℕ+) (h : (D : ℕ) ∣ N) : ZMod.castHom h (ZMod D) (z N) = z D := z.2 ..

@[ext]
lemma ext (x y : ZHat) (h : ∀ n : ℕ+, x n = y n) : x = y := by
  cases x
  cases y
  congr
  ext n
  apply h

lemma ext_iff (x y : ZHat) : (∀ n : ℕ+, x n = y n) ↔ x = y :=
  ⟨ext x y, fun h n => by exact congrFun (congrArg DFunLike.coe h) n⟩

@[simp] lemma zero_val (n : ℕ+) : (0 : ZHat) n = 0 := rfl
@[simp] lemma one_val (n : ℕ+) : (1 : ZHat) n = 1 := rfl
@[simp] lemma ofNat_val (m : ℕ) [m.AtLeastTwo] (n : ℕ+) :
  (OfNat.ofNat m : ZHat) n = (OfNat.ofNat m : ZMod n) := rfl
@[simp] lemma natCast_val (m : ℕ) (n : ℕ+) : (m : ZHat) n = (m : ZMod n) := rfl

instance commRing : CommRing ZHat := inferInstance

--wooah, `import Mathlib` breaks this. TODO test this again after bump to Lean v4.8
lemma zeroNeOne : (0 : ZHat) ≠ 1 := by
  intro h
  have h2 : (0 : ZHat) 2 = (1 : ZHat) 2 := by simp [h]
  rw [zero_val, one_val] at h2
  revert h2 ; decide

instance nontrivial : Nontrivial ZHat := ⟨0, 1, zeroNeOne⟩

instance charZero : CharZero ZHat := ⟨ fun a b h ↦ by
  rw [← ext_iff] at h
  specialize h ⟨_, (max a b).succ_pos⟩
  apply_fun ZMod.val at h
  rwa [natCast_val, ZMod.val_cast_of_lt, natCast_val, ZMod.val_cast_of_lt] at h
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  ⟩
--lemma NonAssocSemiring.Nontrivial_iff (R : Type) [NonAssocSemiring R] :
--    Nontrivial R ↔ (0 : R) ≠ 1 :=
--  ⟨fun _ ↦ zero_ne_one' R, fun a ↦ ⟨0, 1, a⟩⟩

open BigOperators Nat Finset in
/-- A nonarchimedean analogue $0! + 1! + 2! + \cdots$ of $e=1/0! + 1/1! + 1/2! + \cdots$. -/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i in range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  obtain ⟨k, hk⟩ := exists_add_of_le <| le_of_dvd N.pos hDN
  simp_rw [map_sum, map_natCast, hk, sum_range_add, add_right_eq_self]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.dvd_factorial D.pos le_self_add
⟩

open BigOperators Nat Finset in
lemma e_def (n : ℕ+) : e n = ∑ i in range (n : ℕ), (i ! : ZMod n) := rfl

/-- Nonarchimedean $e$ is not an integer. -/
lemma e_not_in_Int : ∀ a : ℤ, e ≠ a := sorry
-- This isn't necessary but isn't too hard to prove.

lemma torsionfree_aux (a b : ℕ) [NeZero b] (h : a ∣ b) (x : ZMod b) (hx : a ∣ x.val) :
    ZMod.castHom h (ZMod a) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  obtain ⟨y, hy⟩ := hx
  rw [hy]
  simp

@[simp]
lemma pnat_mul_apply (N : ℕ+) (z : ZHat) (k : ℕ+) : (N * z) k = N * (z k) := rfl

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := by
  rw [← AddMonoidHom.coe_mulLeft, injective_iff_map_eq_zero]
  intro a ha
  rw [AddMonoidHom.coe_mulLeft] at ha
  rw [← ext_iff]
  intro j
  rw [zero_val, ← a.prop j (N * j) (by simp)]
  apply torsionfree_aux
  apply Nat.dvd_of_mul_dvd_mul_left N.pos
  rw [← PNat.mul_coe]
  apply Nat.dvd_of_mod_eq_zero
  have : N * a (N * j) = 0 := by
    rw [← pnat_mul_apply]
    simp [ha]
  simpa only [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] using congrArg ZMod.val this

lemma y_mul_N_eq_z (N : ℕ+) (z : ZHat) (hz : z N = 0) (j : ℕ+) :
    N * ((z (N * j)).val / (N : ℕ) : ZMod j) = z j := by
  have hhj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
  rw [hz, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hhj
  rw [← Nat.cast_mul, mul_comm, Nat.div_mul_cancel hhj]
  have hhj' := z.prop j (N * j) (by simp only [PNat.mul_coe, dvd_mul_left])
  rw [← hhj']
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

-- LaTeX proof in the notes.
lemma multiples (N : ℕ+) (z : ZHat) : (∃ (y : ZHat), N * y = z) ↔ z N = 0 := by
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    change N * (y N) = 0
    simp [ZMod.natCast_self]
  · intro h
    let y : ZHat := {
      val := fun j ↦ (z (N * j)).val / (N : ℕ)
      property := by
        intro j k hjk
        have hj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
        have hk := z.prop N (N * k) (by simp only [PNat.mul_coe, dvd_mul_right])
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hj
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hk
        have hNjk := z.prop (N * j) (N * k) (mul_dvd_mul (dvd_refl _) hjk)
        rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hNjk
        simp only [PNat.mul_coe, map_natCast, ZMod.natCast_val, ZMod.eq_iff_modEq_nat]
        apply Nat.ModEq.mul_right_cancel' (c := N) (by simp)
        rw [Nat.div_mul_cancel hj, Nat.div_mul_cancel hk,
          mul_comm (j : ℕ) (N : ℕ), ← ZMod.eq_iff_modEq_nat, hNjk]
        simp
    }
    refine ⟨y, ?_⟩
    ext j
    exact y_mul_N_eq_z N z h j


end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

noncomputable example : QHat := (22 / 7) ⊗ₜ ZHat.e

namespace QHat

lemma mul_swap (z : ℤ) (b : ℚ) (x : ZHat) : ((z * b) ⊗ₜ x : QHat) = b ⊗ₜ ((z) • x) := by
  rw [@TensorProduct.tmul_smul]
  rw [@TensorProduct.smul_tmul']
  simp only [zsmul_eq_mul]

lemma canonicalForm (z : QHat) : ∃ (N : ℕ+) (z' : ZHat), z = (1 / N : ℚ) ⊗ₜ z' := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | tmul q z =>
    refine ⟨⟨q.den, q.den_pos ⟩, q.num * z, ?_⟩
    simp only [← zsmul_eq_mul, TensorProduct.tmul_smul]
    simp only [PNat.mk_coe, zsmul_eq_mul]
    congr
    · simp only [← q.mul_den_eq_num, LinearMap.mul_apply', mul_assoc,
        one_div, ne_eq, Nat.cast_eq_zero, Rat.den_ne_zero, not_false_eq_true,
        mul_inv_cancel, mul_one]
    · simp
  | add x y hx hy =>
    obtain ⟨N₁, z₁, rfl⟩ := hx
    obtain ⟨N₂, z₂, rfl⟩ := hy
    refine ⟨N₁ * N₂, (N₁ : ℤ) * z₂ + (N₂ : ℤ) * z₁, ?_⟩
    simp only [TensorProduct.tmul_add, ← zsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [one_div, PNat.mul_coe, Nat.cast_mul, mul_inv_rev, zsmul_eq_mul, Int.cast_natCast,
      ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
    rw [add_comm]
    congr
    simp [mul_comm]

def IsCoprime (N : ℕ+) (z : ZHat) : Prop := IsUnit (z N)

open ZMod in
lemma isUnit_iff_coprime (n : ℕ) (m : ZMod n) : IsUnit m ↔ m.val.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  have H' := val_coe_unit_coprime H.unit
  rwa [IsUnit.unit_spec] at H'
  let m' : (ZMod n)ˣ := {
    val := m
    inv := m⁻¹
    val_inv := by rw [mul_inv_eq_gcd, H.gcd_eq_one, Nat.cast_one]
    inv_val := by rw [mul_comm, mul_inv_eq_gcd, H.gcd_eq_one, Nat.cast_one]
  }
  use m'

lemma isCoprime_iff_coprime (N : ℕ+) (z : ZHat) : IsCoprime N z ↔ Nat.Coprime N (z N).val := by
  unfold IsCoprime
  rw [isUnit_iff_coprime, Nat.coprime_comm]

noncomputable abbrev i₁ : ℚ →ₐ[ℤ] QHat := Algebra.TensorProduct.includeLeft
lemma injective_rat :
    Function.Injective i₁ := sorry -- flatness

noncomputable abbrev i₂ : ZHat →ₐ[ℤ] QHat := Algebra.TensorProduct.includeRight
lemma injective_zHat :
    Function.Injective i₂ := sorry -- flatness

lemma lowestTerms (x : QHat) : (∃ N z, IsCoprime N z ∧ x = (1 / N : ℚ) ⊗ₜ z) ∧
    (∀ N₁ N₂ z₁ z₂,
    IsCoprime N₁ z₁ ∧ IsCoprime N₂ z₂ ∧ (1 / N₁ : ℚ) ⊗ₜ z₁ = (1 / N₂ : ℚ) ⊗ₜ[ℤ] z₂ →
      N₁ = N₂ ∧ z₁ = z₂) := by
  constructor
  · obtain ⟨N, z, h⟩ := canonicalForm x
    let D : PNat := ⟨Nat.gcd N (z N).val, Nat.gcd_pos_of_pos_left _ N.pos⟩
    have : 1 ≤ D := by
      apply PNat.one_le
    cases D.one_le.eq_or_gt with
    | inl hD =>
      use N, z, ?_, h
      simp_rw [D, ← PNat.coe_eq_one_iff, PNat.mk_coe] at hD
      rwa [isCoprime_iff_coprime, Nat.coprime_iff_gcd_eq_one]
    | inr hD =>
      have hDN : D ∣ N := PNat.dvd_iff.mpr (Nat.gcd_dvd_left N (z N).val)
      have hDzN : (D : ℕ) ∣ (z N).val := (Nat.gcd_dvd_right N (z N).val)
      obtain ⟨E, hE⟩  := id hDN
      let zz := z D
      have := z.prop D N (PNat.dvd_iff.mp hDN)
      have : z D = 0 := by
        rwa [← this, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd]

      obtain ⟨y, hy⟩ : ∃ y, D * y = z := by
        rwa [ZHat.multiples]

      have hy' : z N = D * y N := by
        rw [← hy, ZHat.pnat_mul_apply]
      use E, y, ?_, ?_
      · rw [isCoprime_iff_coprime]
        apply Nat.coprime_of_dvd fun k hk hk1 hk2 => ?_
        have : D * k ∣ D := by
          apply dvd_gcd
          · rw [hE]
            simp only [PNat.mul_coe]
            apply mul_dvd_mul_left _ hk1
          · rw [hy']
            rw [@ZMod.val_mul]
            simp [hDN]
            by_cases hDN' : D = N
            · simp [hDN']
            · have := lt_of_le_of_ne (Nat.le_of_dvd N.pos (PNat.dvd_iff.mp hDN)) (by simpa)
              rw [hE]
              simp only [PNat.mul_coe]
              rw [Nat.mul_mod_mul_left]
              apply mul_dvd_mul_left
              rw [Nat.dvd_mod_iff hk1]
              suffices k ∣ (y N).val by
                rw [hE] at this
                simpa


              sorry
        have := Nat.le_of_dvd D.pos this
        apply this.not_lt
        refine (Nat.lt_mul_iff_one_lt_right D.pos).mpr hk.one_lt

      · rw [h, hE, ← hy]
        simp only [PNat.mul_coe, Nat.cast_mul, one_div, mul_inv]
        rw [← smul_eq_mul]
        rw [← smul_eq_mul]
        have : (D : ZHat) • y = (D : ℤ) • y := by
          rw [smul_eq_mul]
          rw [@zsmul_eq_mul]
          simp only [Int.cast_natCast]
        rw [this]
        rw [← TensorProduct.smul_tmul]
        simp
  · intros N₁ N₂ z₁ z₂ h'
    have : 1 ⊗ₜ (N₁ * z₁) = (1 : ℤ) ⊗ₜ[ℤ] (N₂ * z₂) := sorry
    have : i₂ (N₁ * z₁) = i₂ (N₂ * z₂) := sorry
    let y := (N₁ * z₁)
    have hNz := injective_zHat this
    have hy₁ : y = N₁ * z₁ := rfl
    have hy₂ : y = N₂ * z₂ := by rw [← hNz]
    let L : ℕ+ := PNat.lcm N₁ N₂
    have : y L = 0 := by
      suffices (L : ℕ) ∣ (y L).val by sorry
      apply lcm_dvd
      · rw [hy₁]
        simp only [ZHat.pnat_mul_apply]
        rw [ZMod.val_mul]
        simp [PNat.dvd_lcm_left N₁ N₂]
        refine (Nat.dvd_mod_iff ?_).mpr ?_
        simp [Nat.dvd_lcm_left N₁ N₂, L]
        exact Nat.dvd_mul_right _ _
      · rw [hy₂]
        simp only [ZHat.pnat_mul_apply]
        rw [ZMod.val_mul]
        simp [PNat.dvd_lcm_right N₁ N₂]
        refine (Nat.dvd_mod_iff ?_).mpr ?_
        simp [Nat.dvd_lcm_right N₁ N₂, L]
        exact Nat.dvd_mul_right _ _
    obtain ⟨x, hx⟩ := (ZHat.multiples _ _).mpr this
    obtain ⟨M₁, hM₁⟩ : N₁ ∣ L := PNat.dvd_lcm_left N₁ N₂
    obtain ⟨M₂, hM₂⟩ : N₂ ∣ L := PNat.dvd_lcm_right N₁ N₂
    have hz₁ : z₁ = M₁ * x := by
      apply ZHat.torsionfree N₁
      dsimp
      rw [← hy₁, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hM₁]
    have hz₂ : z₂ = M₂ * x :=  by
      apply ZHat.torsionfree N₂
      dsimp
      rw [← hy₂, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hM₂]
    have hN₁ : L = N₁ := sorry
    have hN₂ : L = N₂ := sorry
    have hM : M₁ = M₂ := by
      rw [← PNat.coe_inj]
      apply Nat.mul_left_cancel L.pos
      rw [← PNat.mul_coe]
      rw [← PNat.mul_coe]
      rw [PNat.coe_inj]
      conv_lhs =>
        rw [hN₁, ← hM₁]
      conv_rhs =>
        rw [hN₂, ← hM₂]
    rw [hz₁, hz₂, ← hN₁, ← hN₂, hM]
    exact ⟨rfl, rfl⟩

section additive_structure_of_QHat

noncomputable abbrev ratsub : AddSubgroup QHat :=
    (i₁ : ℚ →+ QHat).range

noncomputable abbrev zHatsub : AddSubgroup QHat :=
    (i₂ : ZHat →+ QHat).range

noncomputable abbrev zsub : AddSubgroup QHat :=
  (Int.castRingHom QHat : ℤ →+ QHat).range

lemma rat_meet_zHat : ratsub ⊓ zHatsub = zsub := sorry

lemma rat_join_zHat : ratsub ⊔ zHatsub = ⊤ := sorry

end additive_structure_of_QHat

section multiplicative_structure_of_QHat

noncomputable abbrev unitsratsub : Subgroup QHatˣ :=
  (Units.map (i₁ : ℚ →* QHat)).range

noncomputable abbrev unitszHatsub : Subgroup QHatˣ :=
  (Units.map (i₂ : ZHat →* QHat)).range

noncomputable abbrev unitszsub : Subgroup QHatˣ :=
  (Units.map (Int.castRingHom QHat : ℤ →* QHat)).range

lemma unitsrat_meet_unitszHat : unitsratsub ⊓ unitszHatsub = unitszsub := sorry

-- this needs that ℤ is a PID.
lemma unitsrat_join_unitszHat : unitsratsub ⊔ unitszHatsub = ⊤ := sorry

end multiplicative_structure_of_QHat
end QHat
