import Mathlib.LinearAlgebra.TensorProduct.Pi

-- #29723
theorem TensorProduct.piScalarRight_symm_algebraMap (R S N ι : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring N] [Algebra R N] [Algebra S N]
    [IsScalarTower R S N] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (TensorProduct.piScalarRight R S N ι).symm (fun i => algebraMap _ _ (x i)) = 1 ⊗ₜ[R] x := by
  simp [LinearEquiv.symm_apply_eq, Algebra.algebraMap_eq_smul_one]
