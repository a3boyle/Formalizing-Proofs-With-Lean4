/-
# Loewner Ordering of the Space of n×n Hermitian Matrices

Denote by ℍⁿ to be the space of n×n Hermitian matrices, and let X ∈ ℍⁿ. Since the eigenvalues
of Hermitian matrices are real, we can order the eigenvalues of X as λₙ(X)≤ ⋯ ≤ λ₁(X).
On this observation we denote by λ(X) = (λ₁(X),⋯,λₙ(X))∈ ℝⁿ the n-tuple of the n real
eigenvalues for X. Also, we denote by Diag(λ(X)) to be the n×n diagonal matrix whose
diagonal is given by λ(X). Furthermore, by the  Spectral Decomposition theorem there exists an
orthonormal basis of ℂⁿ consisting of eigenvectors for X. Denote such basis by B = {q₁,⋯,qₙ}
and let Q = [q₁ | ⋯ | qₙ] be the n×n complex matrix whose columns are determined by the basis B.
Then, it is easy to see that X = QDiag(λ(X))Qᴴ where Qᴴ denotes the conjugate transpose of Q.

We say X ∈ ℍⁿ is positive semidefinite (PSD) if zᴴXz ≥ 0 for all z ∈ ℂⁿ. Similarly, we say that X
is postive definite (PD) if zᴴXz > 0 for all z ∈ ℂⁿ\ {0}. We will denote the space of n×n PSD matrices
by ℍⁿ₊ and the space of n × n PD matrices by ℍⁿ₊₊. It is easy to show that X is PSD if and only if λ(X)≥ 0,
and X is PD if and only if λ(X) > 0. Whence, for a PSD matrix X we define  √X := QDiag(√λ(X))Qᴴ where
√λ(X) := (√λ₁(X),⋯,√λₙ(X)). It is easy to show that √X is positive semidefinite and √X * √X = X.

For n×n Hermitian matrices X and S, we declare that X ≼ S if S - X is positive semidefinite. An interesting
results, is that if 0 ≼ X ≼ S then √X ≼ √S. In other words the map f : ℍⁿ₊ → ℍⁿ₊ given by f(X) = √X
is operator monotone, which is to say that if X,S ∈ ℍⁿ₊ such that X ≼ S, then f(x) ≼ f(S). 

I ran into quite a few issues with this formalization. Most notably, to define the Loewner ordering
on the space of n×n Hermitian matrices, I defined a new type HermitianMatrix n 𝕜, and defined the 
ordering on objects of such type. However, much of the machinery in Mathlib relating to Hermitian 
and PSD matrices is stated in terms of objects of type Matrix n n 𝕜 satisfying the Hermitian and 
PSD predicates. I found it quite difficult to make my formalization consistent/compatible with 
the existing architecture for Hermitian and PSD matrices in Mathlib. I have more comments relating
to my difficulties later in the document. -/

import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.Algebra.Star.Basic

open scoped ComplexOrder
namespace Matrix

variable {n n 𝕜 : Type*}
variable [Fintype n][DecidableEq n]
variable [CommRing R][PartialOrder R][StarRing R][StarOrderedRing R]
variable [RCLike 𝕜]

open scoped Matrix

def HermitianMatrix(n 𝕜: Type*)[Fintype n][DecidableEq n][RCLike 𝕜] := { A : Matrix n n 𝕜 // A.IsHermitian }

/- For X,S ∈ ℍⁿ we define X ≼ S to mean that S - X is positive semidefinite.
The following shows that this ordering is a partial ordering of ℍⁿ. -/
instance {n 𝕜: Type*}[Fintype n][DecidableEq n][RCLike 𝕜] : PartialOrder (HermitianMatrix n 𝕜) where
  le S X := (X.1 - S.1).PosSemidef
  le_refl X := by
    have h₀ : (X.1 - X.1).PosSemidef := by
      simp only [sub_self]
      exact PosSemidef.zero
    exact h₀
  le_trans := by
    intro X1 X2 X3 X1leX2 X2leX3
    have h₀ := PosSemidef.add X1leX2 X2leX3
    simp at h₀
    tauto
  
  /- This is a little tricky. The (unfinished) proof below relies on the fact that if X
  is positive semidefinite, then xᴴXx = 0 ↔ Xx = 0. I struggled to piece together the 
  details of the proof below, as it is a bit technical  -/
  le_antisymm := by 
    intro X S XleS SleX
    have h₀ : (S.1 - X.1).PosSemidef := by 
      exact XleS
    have h₁ : (X.1 - S.1).PosSemidef := by 
      exact SleX
    have h₅ := h₀.dotProduct_mulVec_zero_iff
    unfold PosSemidef at h₀
    unfold PosSemidef at h₁
    have h₂ := h₀.2
    have h₃ := h₁.2
    have h₄ : ∀ (x : n → 𝕜), S.1 *ᵥ x = X.1 *ᵥ x := by 
      intro x 
      have h₅ : star x ⬝ᵥ (S.1 - X.1) *ᵥ x  = 0:= by 
        have h₆ : 0 ≤ star x ⬝ᵥ (S.1 - X.1) *ᵥ x  := by 
          exact h₂ x
        have h₇ : 0 ≤ star x ⬝ᵥ (X.1 - S.1) *ᵥ x  := by 
          exact h₃ x
        have h₈ := Eq.symm (neg_sub X.1 S.1)
        rw[h₈] at h₆
        have h₉ := dotProduct_neg (star x) ((X.1 - S.1) *ᵥ x)
        have h10 := Eq.symm (neg_mulVec x (X.1 - S.1))
        rw[←h10] at h₆
        rw[h₉] at h₆
        have h11 : 0 ≥ star x ⬝ᵥ (X.1 - S.1) *ᵥ x := by 
          exact neg_nonneg.mp h₆
        sorry
      have h₆ : (S.1 - X.1) *ᵥ x = 0:= by 
        exact (PosSemidef.dotProduct_mulVec_zero_iff XleS x).mp h₅
      sorry
    sorry
    
section PSD
variable {n : Type*} [Fintype n][DecidableEq n] {X S: HermitianMatrix n 𝕜}  

/- This following are trivial lemmas to make our life easier -/
theorem LoewnerOrder_le_iff_diff_PSD : S ≤ X ↔ (X.1 - S.1).PosSemidef := Iff.rfl

/- If X ∈ ℍⁿ₊₊ then det X ≠ 0. This follows from the fact that positive definite 
matrices have positive eigenvalues, and that the determinant of an n×n matrix
is equal to the product of its eigenvalues  -/
theorem PD_implies_nonzero_det (Xpd : X.1.PosDef) : det X.1 ≠ 0 := by
  have detpos := Xpd.det_pos 
  exact (fun a a_1 ↦ Ne.symm (ne_of_lt a_1)) (X.1.det) detpos

/- The previous theorem implies that det X ≠ 0 for any X ∈ ℍⁿ₊₊. Thus
any positive definite matrix is invertible. -/
theorem PD_implies_invertible (Xpd : X.1.PosDef): IsUnit (X.1) := by
  have detNonZero := PD_implies_nonzero_det Xpd
  have detUnit : IsUnit (det X.1) := by 
    exact Ne.isUnit detNonZero
  exact (isUnit_iff_isUnit_det X.1).mpr detUnit

/- Positive definite matrices are invertible, and hence have full rank. -/
theorem PD_implies_full_rank (Xpd: X.1.PosDef) : X.1.rank = Fintype.card n := by
  have XInv := PD_implies_invertible Xpd
  exact rank_of_isUnit X.1 XInv

/- Suppose that X and S are n×n Hermitian matrices such that 0 ≼ X ≼ S. Then, 0 ≼ S. -/
theorem GePSDImpliesPSD (Xpsd : X.1.PosSemidef)
(XleS : X ≤ S) : S.1.PosSemidef := by
  have h₀ : (S.1 - X.1 + X.1).PosSemidef := by 
    exact PosSemidef.add XleS Xpsd
  simp at h₀
  exact h₀

/-Suppose that X and S are n×n Hermitian matrices such that that X ≼ S and X is PD. Then, S is PD. -/
theorem PD_ge_implies_PD (Xpd : X.1.PosDef) (XleS : X ≤ S) : S.1.PosDef := by
  have h₀ : (S.1 - X.1 + X.1).PosDef := by
    exact PosDef.posSemidef_add XleS Xpd
  simp at h₀
  exact h₀

/- The following proves that the trace of an n×n Hermitian matrix X is equal to the sum of its eigenvalues. 
Of course this is true for any n×n matrix, but for simplicity, it is stated in terms of Hermitian matrices.
Unortunately, I did not get to completing this proof. -/
theorem trace_eq_sum_eigenvalues : X.1.trace = ∑ i, (X.2.eigenvalues i : 𝕜) := by
  sorry

/-If X is PSD, then its trace is nonnegative. This is a trivial consequence of the fact
that the eigenvalues of a PSD matrix are nonnegative. -/
theorem PSDTraceNonNeg (Xpsd : X.1.PosSemidef) : X.1.trace ≥ 0 := by
  have h₀ := Xpsd.eigenvalues_nonneg
  have h₁ : 0 ≤ ∑ i, (Xpsd.1.eigenvalues i : 𝕜) := by
    refine Finset.sum_nonneg ?h
    simp
    exact fun i ↦ h₀ i
  exact le_of_le_of_eq h₁ (id (Eq.symm trace_eq_sum_eigenvalues))

/-The following theorem proves that X is positive semidefinite if and only if Tr(XS) is nonnegative
for all positive semidefintie matrices S. 

As mentioned early in the document, I ran into issues relating to formalizing the Loewner ordering on ℍⁿ. 
Originally, I started the following proof assuming that the objects X and S were of type Matrix n n 𝕜, and that
the ordering ≤ was an ordering of the set of all n×n matrices with entries from 𝕜. However, the Loewner ordering
is defined on the space of all n×n Hermitian matrices, and upon introducing the type HermitianMatrix n 𝕜, and 
defining the ordering ≤ on objects of type HermitianMatrix n 𝕜, the following (incomplete) proof breaks down. 

In particular, the positive semidefinite squareroot (in Mathlib.LinearAlgebra.Matrix.PosDef) is defined on 
objects of type Matrix n n 𝕜 that satisfy the PSD predicate. Thus, to fix the following issues, I would likely 
need to redefine the positive semidefinite squareroot (and reprove some important consequences) on objects of 
type HermitianMatrix n 𝕜 that satisfy the PSD predicate. -/

theorem PSDiffTraceProdNonNeg (X : HermitianMatrix n 𝕜)
  : X.1.PosSemidef ↔ ∀ (S : HermitianMatrix n 𝕜), S.1.PosSemidef → (X.1 * S.1).trace ≥ 0 := by
  refine⟨?_,?_⟩
  intro Xpsd Spsd
  have h₀ : X * S = X * Spsd.sqrt * Spsd.sqrt := by 
    have h₂ : S = Spsd.sqrt * Spsd.sqrt := by
      exact Eq.symm (PosSemidef.sqrt_mul_self Spsd)
    simp only [h₂]
    exact Eq.symm (Matrix.mul_assoc X Spsd.sqrt Spsd.sqrt)
  rw[h₀]
  have h₁ := trace_mul_cycle X (Spsd.sqrt) (Spsd.sqrt)
  rw[h₁]
  have h₂ : (Spsd.sqrt * X * Spsd.sqrt).PosSemidef := by
    unfold PosSemidef
    refine⟨?_,?_⟩
    have h₃ := (PosSemidef.posSemidef_sqrt Spsd).1
    unfold IsHermitian at h₃
    nth_rw 2 [←h₃]
    apply isHermitian_mul_mul_conjTranspose Spsd.sqrt XHerm
    intro x
    have SsqrtPSD := Spsd.posSemidef_sqrt
    have SsqrtHerm := SsqrtPSD.1

    /- Using the fact that X is PSD, we show that 0 ≤ (√Sx)ᴴX(√Sx) for any x-/
    have h₄ : 0 ≤ (star (Spsd.sqrt *ᵥ x)) ⬝ᵥ (X *ᵥ (Spsd.sqrt *ᵥ x)) := by
      exact Xpsd.2 (Spsd.sqrt *ᵥ x)

    /- Now we show that xᴴ(√SX√S)x = (√Sx)ᴴX(√Sx) -/
    have h₅ : (star x) ⬝ᵥ ((Spsd.sqrt * X * Spsd.sqrt) *ᵥ x)
    = (star (Spsd.sqrt *ᵥ x)) ⬝ᵥ (X *ᵥ (Spsd.sqrt *ᵥ x)) := by
      have h₆ := dotProduct_mulVec (star x) Spsd.sqrt (X *ᵥ (Spsd.sqrt *ᵥ x))
      simp only [mulVec_mulVec] at h₆
      rw[mul_assoc]
      simp only [mulVec_mulVec]
      have h₈ := Spsd.sqrt.mulVec_conjTranspose x
      have h₉ := star_star (star x ᵥ* Spsd.sqrt)
      rw[←h₈] at h₉
      rw[←h₉] at h₆
      rwa[SsqrtHerm] at h₆
    exact le_of_le_of_eq h₄ (id (Eq.symm h₅))
  exact PSDTraceNonNeg h₂
  intro TrNonNeg
  unfold PosSemidef
  refine⟨?_,?_⟩
  exact XHerm
  intro x
  sorry

/- I never was able to actually formalize the following proof
(again relating to my issues formalizing the Loewener ordering).
A proof can be found on page 115 of Bhatia's Matrix Analysis. -/

theorem sqrtInvertOpMonotone (Xpd : X.1.PosDef) (Spsd : S.1.PosSemidef)
(XleS : X ≤ S) : Xpd.sqrt ≤ Spsd.sqrt := by
  sorry

/- Note that the theorem statement above supposes that X is PD. 
However,  we can prove operator monotonicity of the PSD squareroot in the case 
in which the matrix X is PSD but not necessarily PD using the above theorem.
Indeed, If 0 ≼ X ≼ S then (X + εI) is PD and (X + εI) ≼ (S + εI). Therefore,
√(X + εI) ≼ √(S + εI), and taking ε → 0 and appealing to continuity 
of the map X ↦ √X concludes the result. However, there is a lot going on here,
 and it would likely take some time to formalize.
-/