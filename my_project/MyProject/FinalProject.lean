/-
# Loewner Ordering of the Space of n×n Hermitian Matrices
# Written by: Aidan Boyle

Denote by ℍⁿ to be the space of n×n Hermitian matrices, and let X ∈ ℍⁿ. Since the eigenvalues
of Hermitian matrices are real, we can order the eigenvalues of X as λₙ(X)≤ ⋯ ≤ λ₁(X).
On this observation we denote by λ(X) = (λ₁(X),⋯,λₙ(X))∈ ℝⁿ the n-tuple of the n real
eigenvalues for X. Also, we denote by Diag(λ(X)) to be the n×n diagonal matrix whose
diagonal is given by λ(X). Furthermore, by the  Spectral Decomposition theorem there exists an
orthonormal basis of ℂⁿ consisting of eigenvectors for X. Denote such basis by B = {q₁,⋯,qₙ}
and let Q = [q₁ | ⋯ | qₙ] be the n × n complex matrix whose columns are determined by the basis B.
Then, it is easy to see that X = QDiag(λ(X))Qᴴ where Qᴴ denotes the conjugate transpose of Q.

We say X ∈ ℍⁿ is positive semidefinite (PSD) if zᴴXz ≥ 0 for all z ∈ ℂⁿ. Similarly, we say that X
is postive definite (PD) if zᴴXz > 0 for all z ∈ ℂⁿ\ {0}. We will denote the space of n×n PSD matrices
by ℍⁿ₊ and the space of n × n PD matrices by ℍⁿ₊₊. It is easy to show that X is PSD if and only if λ(X)≥ 0,
and X is PD if and only if λ(X) > 0. Whence, for a PSD matrix X we define  √X := QDiag(√λ(X))Qᴴ where
√λ(X) := (√λ₁(X),⋯,√λₙ(X)). It is easy to show that √X is positive semidefinite and √X * √X = X.

For n×n Hermitian matrices X and S, we declare that X ≼ S if S - X is positive semidefinite. An interesting
result, is that if 0 ≼ X ≼ S then √X ≼ √S. In other words the map f : ℍⁿ₊ → ℍⁿ₊ given by f(X) = √X
is operator monotone, which is to say that if X,S ∈ ℍⁿ₊ such that X ≼ S, then f(x) ≼ f(S).-/

import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Matrix.Invertible
import Mathlib.Algebra.Star.Basic

open scoped ComplexOrder
namespace Matrix

variable {n n 𝕜 : Type*}
variable [Fintype n][DecidableEq n]
variable [CommRing R][PartialOrder R][StarRing R][StarOrderedRing R]
variable [RCLike 𝕜]

open scoped Matrix

/- For X,S ∈ ℍⁿ we define X ≼ S to mean that S - X is positive semidefinite.
The following shows that this ordering is a partial ordering of ℍⁿ. For the
sake of simplicty of the formalization, we define the Loewner odering
on the space of n by n matrices with entries from 𝕜. -/
instance : PartialOrder (Matrix n n 𝕜) where
  le S X := (X - S).PosSemidef
  le_refl X := by
    have h₀ : (X - X).PosSemidef := by
      simp only [sub_self]
      exact PosSemidef.zero
    exact h₀
  le_trans := by
    intro X1 X2 X3 X1leX2 X2leX3
    have h₀ := PosSemidef.add X1leX2 X2leX3
    simp at h₀
    tauto

  /- This is a little tricky. The proof below relies on the fact that if X
  is positive semidefinite, then xᴴXx = 0 ↔ Xx = 0. -/
  le_antisymm := by
    intro X S XleS SleX
    have h₀ : (S - X).PosSemidef := by
      exact XleS
    have h₁ : (X - S).PosSemidef := by
      exact SleX
    unfold PosSemidef at h₀
    unfold PosSemidef at h₁
    have h₂ := h₀.2
    have h₃ := h₁.2
    have h₄ : ∀ (x : n → 𝕜), X *ᵥ x = S *ᵥ x := by
      intro x
      have h₅ : star x ⬝ᵥ (X - S) *ᵥ x  = 0:= by
        have h₆ := h₂ x
        rw[Eq.symm (neg_sub X S), ←Eq.symm (neg_mulVec x (X - S)),
        dotProduct_neg (star x) ((X - S) *ᵥ x)] at h₆
        exact le_antisymm (neg_nonneg.mp h₆) (h₃ x)
      have h₆ : (X - S) *ᵥ x = 0 := by
        exact (PosSemidef.dotProduct_mulVec_zero_iff SleX x).mp h₅
      rwa[sub_mulVec, sub_eq_zero] at h₆
    ext i j

    /- Consider the jth standard basis vector for 𝕜ⁿ -/
    let e_j : n → 𝕜 := fun k ↦ if k = j then 1 else 0
    have h₉ : ∀ (X: Matrix n n 𝕜), ∀ i, (X *ᵥ e_j) i = X i j := by
      simp_rw[mulVec, dotProduct, e_j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
      tauto
    rw[←(h₉ X), ← (h₉ S)]
    exact (fun i ↦ congrFun (h₄ e_j) i) i

section PSD

variable {n : Type*} [Fintype n][DecidableEq n] [RCLike 𝕜] {X S: Matrix n n 𝕜}

/- This following are trivial lemmas to make our life easier -/
theorem LoewnerOrder_le_iff_diff_PSD : S ≤ X ↔ (X - S).PosSemidef := Iff.rfl

/- If X ∈ ℍⁿ₊₊ then det X ≠ 0. This follows from the fact that positive definite
matrices have positive eigenvalues, and that the determinant of an n×n matrix
is equal to the product of its eigenvalues  -/
theorem PD_implies_nonzero_det (Xpd : X.PosDef) : det X ≠ 0 := by
  have detpos := Xpd.det_pos
  exact (fun a a_1 ↦ Ne.symm (ne_of_lt a_1)) (X.det) detpos

/- The previous theorem implies that det X ≠ 0 for any X ∈ ℍⁿ₊₊. Thus
any positive definite matrix is invertible. -/
theorem PD_implies_invertible (Xpd : X.PosDef): IsUnit (X) := by
  have detNonZero := PD_implies_nonzero_det Xpd
  have detUnit : IsUnit (det X) := by
    exact Ne.isUnit detNonZero
  exact (isUnit_iff_isUnit_det X).mpr detUnit

/- Positive definite matrices are invertible, and hence have full rank. -/
theorem PD_implies_full_rank (Xpd: X.PosDef) : X.rank = Fintype.card n := by
  have XInv := PD_implies_invertible Xpd
  exact rank_of_isUnit X XInv

/- Suppose that X and S are n×n Hermitian matrices such that 0 ≼ X ≼ S. Then, 0 ≼ S. -/
theorem GePSDImpliesPSD (Xpsd : X.PosSemidef)
(XleS : X ≤ S) : S.PosSemidef := by
  have h₀ : (S - X + X).PosSemidef := by
    exact PosSemidef.add XleS Xpsd
  simp at h₀
  exact h₀

/-Suppose that X and S are n×n Hermitian matrices such that that X ≼ S and X is PD.
Then, S is PD. -/
theorem PD_ge_implies_PD (Xpd : X.PosDef) (XleS : X ≤ S) : S.PosDef := by
  have h₀ : (S - X + X).PosDef := by
    exact PosDef.posSemidef_add XleS Xpd
  simp at h₀
  exact h₀

/- The following proves that the trace of an n×n Hermitian matrix X is equal
to the sum of its eigenvalues. Of course this is true for any n×n matrix, but for
simplicity, it is stated in terms of Hermitian matrices.-/
theorem trace_eq_sum_eigenvalues (hHerm : X.IsHermitian)
: X.trace = ∑ i, (hHerm.eigenvalues i : 𝕜) := by
  have h₀ := hHerm.spectral_theorem
  let Q : Matrix n n 𝕜 := ↑hHerm.eigenvectorUnitary
  let D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hHerm.eigenvalues)
  have h₀ : X.trace = (Q * D * (star  Q)).trace := by
    exact congrArg trace h₀
  rw[Eq.symm (trace_mul_cycle D (star Q) Q)] at h₀
  have h₁ : D * 1 = D := by
    exact Matrix.mul_one D
  rw[←UnitaryGroup.star_mul_self hHerm.eigenvectorUnitary] at h₁
  rw[←Matrix.mul_assoc D (star Q) Q] at h₁
  rw[h₁] at h₀
  have h₇ : D.trace =  ∑ i : n, ↑(hHerm.eigenvalues i) := by
    exact trace_diagonal (RCLike.ofReal ∘ hHerm.eigenvalues)
  rwa[h₀]

/-If X is PSD, then its trace is nonnegative. This is a trivial consequence of the fact
that the eigenvalues of a PSD matrix are nonnegative. -/
theorem PSDTraceNonNeg (Xpsd : X.PosSemidef) : X.trace ≥ 0 := by
  have h₀ := Xpsd.eigenvalues_nonneg
  have h₁ : 0 ≤ ∑ i, (Xpsd.1.eigenvalues i : 𝕜) := by
    refine Finset.sum_nonneg ?h
    simp
    exact fun i ↦ h₀ i
  exact le_of_le_of_eq h₁ (id (Eq.symm (trace_eq_sum_eigenvalues Xpsd.1)))

/- If X is a positive semidefinite matrix with nonzero determinant, then X
is positive definite. -/
theorem PSDDetNonZeroPD (Xpsd : X.PosSemidef) (detNeZero : X.det ≠ 0) : PosDef X := by 
  constructor
  exact Xpsd.1
  intro x xNeZero
  have nonNeg := Xpsd.2
  have pos : star x ⬝ᵥ X *ᵥ x ≠ 0 := by 
    by_contra!
    have eqZero := (PosSemidef.dotProduct_mulVec_zero_iff Xpsd x).mp this
    have h₀ : ∃ v, v ≠ 0 ∧ X *ᵥ v = 0 := by
      exact Filter.frequently_principal.mp fun a ↦ a xNeZero eqZero
    have h₁ := exists_mulVec_eq_zero_iff_aux.mp h₀
    contradiction
  exact lt_of_le_of_ne (nonNeg x) (id (Ne.symm pos))

/- We now prove that if X and S are posistive definite then so is SXS. The statement
is still true if we only assume that S is square and of full rank, but for simplicity
we state it for S being positive definite.  -/
theorem mulPD_mulPD_same_PD (Xpd : X.PosDef)(Spd : S.PosDef) : PosDef (S * X * S) := by
  constructor
  nth_rw 1 [←Spd.1]
  · exact isHermitian_conjTranspose_mul_mul S Xpd.1
  intro x xNeZero
  have SdetNeZero : det S ≠ 0 := by
    exact PD_implies_nonzero_det Spd
  have h₃ : star S = S := by 
    exact Spd.1
  have SNullTriv : S *ᵥ x ≠ 0 := by
    by_contra!
    have h₁ : S.det = 0:= by 
      have h₂ : ∃ v, v≠ 0 ∧ S *ᵥ v = 0 := by
        exact Filter.frequently_principal.mp fun a ↦ a xNeZero this
      exact exists_mulVec_eq_zero_iff_aux.mp h₂
    exact SdetNeZero h₁
  have h₂ : star x ⬝ᵥ (S * X * S) *ᵥ x = star ( (star S) *ᵥ x) ⬝ᵥ X *ᵥ (S *ᵥ x) := by 
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    rw[h₃, Spd.1]
  rw[h₂]
  nth_rw 1 [h₃]
  exact Xpd.2 (S *ᵥ x) SNullTriv

/- The next theorem shows that the inverse of a positive definite matrix
is positive definite. -/
theorem inv_of_posdef_is_posdef (Xpd : X.PosDef): X⁻¹.PosDef := by 
  have invPSD : X⁻¹.PosSemidef := by
    exact PosSemidef.inv (PosDef.posSemidef Xpd)
  have invDetUnit := isUnit_nonsing_inv_det X (Ne.isUnit (PD_implies_nonzero_det Xpd))
  have invDetNonZero := IsUnit.ne_zero invDetUnit
  exact PSDDetNonZeroPD invPSD invDetNonZero

/- If X is a positive definite matrix, then its positive semidefinite 
square root is positive definite -/
theorem sqrtPD_implies_PD (Xpd: X.PosDef) : PosDef ((Xpd.posSemidef).sqrt) := by 
  have h₀ : (Xpd.posSemidef).sqrt.det^2 = X.det := by  
    simp_rw[← Xpd.posSemidef.sqrt_mul_self, det_mul, pow_two]
  have h₁ : X.det > 0 := by
    exact PosDef.det_pos Xpd
  rw[← h₀] at h₁
  have h₂ : (Xpd.posSemidef).sqrt.det ≠ 0 := by
    by_contra!
    simp_rw[this] at h₁
    linarith
  exact PSDDetNonZeroPD (PosSemidef.posSemidef_sqrt (PosDef.posSemidef Xpd)) h₂
  
/- Given a scalar κ ∈ ℂ and a size n, we define a matrix of size n × n
whose entries are given by κ. -/
def castScalar (κ : 𝕜) (n : Type*) : Matrix n n 𝕜 :=
  of fun _ _ => κ

/- If κ ∈ ℂ then κ = Tr(κ)-/
lemma trace_scalar (κ : 𝕜) : κ = (castScalar κ (Fin 1)).trace := by
  exact Eq.symm (trace_fin_one (castScalar κ (Fin 1)))

/- Given a vector x ∈ ℂⁿ, we define the outer product xxᴴ.-/
def outerProd (x : n → 𝕜) : Matrix n n 𝕜 :=
  of fun i j => (x i) * star (x j)

/- We now prove that the outer product of two vectors in ℂⁿ is Hermitian. -/
theorem outer_prod_Hermitian(x: n → 𝕜) : (outerProd x).IsHermitian := by
  refine IsHermitian.ext_iff.mpr ?_
  unfold outerProd
  simp only [of_apply]
  exact fun i j ↦ star_mul_star (x j) (x i)

/- In particular, xᴴx is positive semidefinite-/
theorem outer_prod_PSD (x: n → 𝕜) : (outerProd x).PosSemidef := by
  let X : Matrix n (Fin 1) 𝕜 := fun i _ ↦ x i
  have Xpsd := posSemidef_self_mul_conjTranspose X
  have OuterProdpsd : (X * Xᴴ) = outerProd x := by
    refine ext ?_
    simp[Matrix.mul_apply]
    exact fun i j ↦ rfl
  rwa[OuterProdpsd] at Xpsd

/- Appealing to two previous lemmas, it follows that xᴴXx = Tr(Xxxᴴ). In particular, this result
will be useful in the proof of the next theorem. -/
lemma cyclic_outer_product_trace (x: n → 𝕜):
(X * (outerProd x)).trace = (star x) ⬝ᵥ (X *ᵥ x):= by
  let Y : Matrix n (Fin 1) 𝕜 := fun i _ ↦ x i
  have OuterProd : (Y * Yᴴ) = outerProd x := by
    refine ext ?_
    simp[Matrix.mul_apply]
    exact fun i j ↦ rfl
  rw[← OuterProd]
  have h₀ := trace_fin_one (Yᴴ * X * Y)
  have h₁ : (Yᴴ * X * Y) 0 0 = (star x) ⬝ᵥ (X *ᵥ x) := by
    simp[Y]
    rw[Matrix.mul_apply, dotProduct_mulVec]
    exact rfl
  have h₂ := Matrix.mul_assoc X Y Yᴴ
  simp [←h₁, ←h₀, ←h₂]
  exact trace_mul_cycle X Y Yᴴ

/-The following theorem proves that X is positive semidefinite if and only if Tr(XS) is nonnegative
for all positive semidefinite matrices S.-/
theorem PSDiffTraceProdNonNeg (XHerm: X.IsHermitian)
  : X.PosSemidef ↔ ∀ (S : Matrix n n 𝕜), S.PosSemidef → (X * S).trace ≥ 0 := by
  refine⟨?_,?_⟩
  intro Xpsd S Spsd
  have h₀ : X * S = X * Spsd.sqrt * Spsd.sqrt := by
    simp only [Eq.symm (PosSemidef.sqrt_mul_self Spsd)]
    exact Eq.symm (Matrix.mul_assoc X Spsd.sqrt Spsd.sqrt)
  rw[h₀, trace_mul_cycle X (Spsd.sqrt) (Spsd.sqrt)]
  have h₁ : (Spsd.sqrt * X * Spsd.sqrt).PosSemidef := by
    unfold PosSemidef
    refine⟨?_,?_⟩
    have h₂ := (PosSemidef.posSemidef_sqrt Spsd).1
    unfold IsHermitian at h₂
    nth_rw 2 [←h₂]
    apply isHermitian_mul_mul_conjTranspose Spsd.sqrt XHerm
    intro x
    have SsqrtPSD := Spsd.posSemidef_sqrt
    have SsqrtHerm := SsqrtPSD.1

    /- Using the fact that X is PSD, we show that 0 ≤ (√Sx)ᴴX(√Sx) for any x-/
    have h₃ : 0 ≤ (star (Spsd.sqrt *ᵥ x)) ⬝ᵥ (X *ᵥ (Spsd.sqrt *ᵥ x)) := by
      exact Xpsd.2 (Spsd.sqrt *ᵥ x)

    /- Now we show that xᴴ(√SX√S)x = (√Sx)ᴴX(√Sx) -/
    have h₄ : (star x) ⬝ᵥ ((Spsd.sqrt * X * Spsd.sqrt) *ᵥ x)
    = (star (Spsd.sqrt *ᵥ x)) ⬝ᵥ (X *ᵥ (Spsd.sqrt *ᵥ x)) := by
      have h₅ := dotProduct_mulVec (star x) Spsd.sqrt (X *ᵥ (Spsd.sqrt *ᵥ x))
      simp only [mulVec_mulVec] at h₅
      simp only [mul_assoc, mulVec_mulVec]
      have h₆ := star_star (star x ᵥ* Spsd.sqrt)
      rw[←Spsd.sqrt.mulVec_conjTranspose x] at h₆
      rw[←h₆] at h₅
      rwa[SsqrtHerm] at h₅
    exact le_of_le_of_eq h₃ (id (Eq.symm h₄))
  exact PSDTraceNonNeg h₁ /- First direction done -/

  /- appealing to the theorem 'cyclic_outer_product_trace',
  helps use prove the backward direction. -/
  intro TrNonNeg
  unfold PosSemidef
  simp [XHerm]
  intro x
  rw[← cyclic_outer_product_trace]
  apply TrNonNeg
  exact outer_prod_PSD x

/- I never was able to actually formalize the following proof
A proof can be found on page 115 of Bhatia's Matrix Analysis. -/
theorem sqrtInvertOpMonotone (Xpd : X.PosDef) (Spsd : S.PosSemidef)
(XleS : X ≤ S) : (Xpd.posSemidef).sqrt ≤ Spsd.sqrt := by
  have Xpsd := Xpd.posSemidef
  have Spd := PD_ge_implies_PD Xpd XleS
  let A : Matrix n n 𝕜 := S * X⁻¹
  let B : Matrix n n 𝕜 := (Xpsd.sqrt)⁻¹
  let C : Matrix n n 𝕜 := B * S * B
  have Bpd :=  inv_of_posdef_is_posdef (sqrtPD_implies_PD Xpd)
 
  /- The matrix C is PD.  -/
  have Cpd : PosDef C := by
    exact mulPD_mulPD_same_PD Spd Bpd
  sorry
  
/- Note that the theorem statement above supposes that X is PD.
However,  we can prove operator monotonicity of the PSD squareroot in the case
in which the matrix X is PSD but not necessarily PD using the above theorem.
Indeed, If 0 ≼ X ≼ S then (X + εI) is PD and (X + εI) ≼ (S + εI). Therefore,
√(X + εI) ≼ √(S + εI), and taking ε → 0 and appealing to continuity
of the map X ↦ √X concludes the result. However, there is a lot going on here,
and it would likely take some time to formalize.-/

theorem sqrtOpMonotone (Xpsd : X.PosSemidef) (Spsd : S.PosSemidef)
(XleS : X ≤ S) : Xpsd.sqrt ≤ Spsd.sqrt := by
  sorry
