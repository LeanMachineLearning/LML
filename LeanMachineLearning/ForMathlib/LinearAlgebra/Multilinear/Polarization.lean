/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Polarization of symmetric multilinear maps

This file proves that a symmetric continuous multilinear map is determined by its values on the
diagonal.  The main input is the existing formula
`ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`: the `n`-th derivative of the diagonal
of an `n`-linear map is the sum of the map over all permutations of its arguments.  For a
symmetric map this sum is `n!` times the original value.

The most general statements only assume that `n!` is nonzero in the scalar field.  Characteristic
zero versions are provided as convenient corollaries.
-/

@[expose] public section

open scoped BigOperators

namespace MultilinearMap

universe uR uM uN uι

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {ι : Type uι}

/-- A multilinear map is symmetric if reindexing its arguments by a permutation leaves it
unchanged. -/
class IsSymm (f : MultilinearMap R (fun _ : ι => M) N) : Prop where
  domDomCongr_eq (σ : Equiv.Perm ι) : f.domDomCongr σ = f

namespace IsSymm

variable {f g : MultilinearMap R (fun _ : ι => M) N}

/-- Pointwise characterization of symmetry. -/
theorem isSymm_iff : f.IsSymm ↔ ∀ (v : ι → M) (σ : Equiv.Perm ι), f (v ∘ σ) = f v where
  mp hf v σ := by
    have h := congrArg (fun p : MultilinearMap R (fun _ : ι => M) N => p v)
      (hf.domDomCongr_eq σ)
    change f (fun i => v (σ i)) = f v at h
    exact h
  mpr h := by
    constructor
    intro σ
    ext v
    change f (v ∘ σ) = f v
    exact h v σ

/-- A symmetric multilinear map has the same value after permuting its arguments. -/
@[simp]
lemma map_perm [hf : f.IsSymm] (v : ι → M) (σ : Equiv.Perm ι) :
    f (v ∘ σ) = f v :=
  isSymm_iff.mp hf v σ

instance zero : IsSymm (0 : MultilinearMap R (fun _ : ι => M) N) where
  domDomCongr_eq _ := by ext; simp

instance add [f.IsSymm] [g.IsSymm] : IsSymm (f + g) where
  domDomCongr_eq σ := by
    ext v
    change f (v ∘ σ) + g (v ∘ σ) = f v + g v
    rw [map_perm, map_perm]

end IsSymm

section Ring

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {ι : Type uι}

namespace IsSymm

variable {f g : MultilinearMap R (fun _ : ι => M) N}

instance neg [f.IsSymm] : IsSymm (-f) where
  domDomCongr_eq σ := by
    ext v
    change -f (v ∘ σ) = -f v
    rw [map_perm]

instance sub [f.IsSymm] [g.IsSymm] : IsSymm (f - g) where
  domDomCongr_eq σ := by
    ext v
    change f (v ∘ σ) - g (v ∘ σ) = f v - g v
    rw [map_perm, map_perm]

end IsSymm

end Ring

end MultilinearMap

namespace ContinuousMultilinearMap

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {n : ℕ}

/-- Symmetry of a continuous multilinear map, inherited from its underlying multilinear map. -/
class IsSymm (f : E [×n]→L[𝕜] F) : Prop extends f.toMultilinearMap.IsSymm

namespace IsSymm

variable {f g : E [×n]→L[𝕜] F}

/-- Pointwise characterization of symmetry for continuous multilinear maps. -/
theorem isSymm_iff : f.IsSymm ↔
    ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = f v where
  mp hf := MultilinearMap.IsSymm.isSymm_iff.mp hf.toIsSymm
  mpr h := by
    have hf : f.toMultilinearMap.IsSymm := MultilinearMap.IsSymm.isSymm_iff.mpr h
    exact { domDomCongr_eq := hf.domDomCongr_eq }

/-- A symmetric continuous multilinear map has the same value after permuting its arguments. -/
@[simp]
lemma map_perm [f.IsSymm] (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    f (v ∘ σ) = f v :=
  isSymm_iff.mp ‹f.IsSymm› v σ

instance zero : IsSymm (0 : E [×n]→L[𝕜] F) where
  domDomCongr_eq _ := by ext; simp

instance add [f.IsSymm] [g.IsSymm] : IsSymm (f + g) where
  domDomCongr_eq σ := by
    ext v
    change f (v ∘ σ) + g (v ∘ σ) = f v + g v
    rw [map_perm, map_perm]

instance neg [f.IsSymm] : IsSymm (-f) where
  domDomCongr_eq σ := by
    ext v
    change -f (v ∘ σ) = -f v
    rw [map_perm]

instance sub [f.IsSymm] [g.IsSymm] : IsSymm (f - g) where
  domDomCongr_eq σ := by
    ext v
    change f (v ∘ σ) - g (v ∘ σ) = f v - g v
    rw [map_perm, map_perm]

/-- Differential form of the polarization identity: for a symmetric `n`-linear map, the `n`-th
derivative of its restriction to the diagonal is `n!` times the original map. -/
theorem factorial_smul_eq_iteratedFDeriv_comp_diagonal [f.IsSymm]
    (x : E) (v : Fin n → E) :
    (n.factorial : 𝕜) • f v =
      iteratedFDeriv 𝕜 n (fun y => f (fun _ => y)) x v := by
  rw [f.iteratedFDeriv_comp_diagonal]
  have hperm : ∀ σ : Equiv.Perm (Fin n), f (fun i => v (σ i)) = f v := by
    intro σ
    change f (v ∘ σ) = f v
    exact map_perm v σ
  simp_rw [hperm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]

end IsSymm

variable {f g : E [×n]→L[𝕜] F}

/-- A symmetric continuous `n`-linear map is zero if it vanishes on the diagonal and `n!` is
nonzero in the scalar field. -/
theorem eq_zero_of_diagonal_eq_zero_of_factorial_ne_zero [f.IsSymm]
    (hn : (n.factorial : 𝕜) ≠ 0) (hdiag : ∀ x : E, f (fun _ => x) = 0) : f = 0 := by
  ext v
  have h := IsSymm.factorial_smul_eq_iteratedFDeriv_comp_diagonal (f := f) (0 : E) v
  have hfun : (fun x : E => f (fun _ => x)) = (fun _ : E => (0 : F)) :=
    funext hdiag
  rw [hfun, iteratedFDeriv_fun_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hn

/-- Over a characteristic-zero nontrivially normed field, a symmetric continuous multilinear map
is zero if it vanishes on the diagonal. -/
theorem eq_zero_of_diagonal_eq_zero [CharZero 𝕜] [f.IsSymm]
    (hdiag : ∀ x : E, f (fun _ => x) = 0) : f = 0 :=
  f.eq_zero_of_diagonal_eq_zero_of_factorial_ne_zero
    (Nat.cast_ne_zero.mpr n.factorial_ne_zero) hdiag

/-- Two symmetric continuous `n`-linear maps agree if their diagonal values agree and `n!` is
nonzero in the scalar field. -/
theorem ext_of_diagonal_of_factorial_ne_zero [f.IsSymm] [g.IsSymm]
    (hn : (n.factorial : 𝕜) ≠ 0)
    (hdiag : ∀ x : E, f (fun _ => x) = g (fun _ => x)) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_diagonal_eq_zero_of_factorial_ne_zero hn
  intro x
  simp only [sub_apply, hdiag x, sub_self]

/-- Over a characteristic-zero nontrivially normed field, symmetric continuous multilinear maps
are determined by their diagonal values. -/
theorem ext_of_diagonal [CharZero 𝕜] [f.IsSymm] [g.IsSymm]
    (hdiag : ∀ x : E, f (fun _ => x) = g (fun _ => x)) : f = g :=
  ext_of_diagonal_of_factorial_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero) hdiag

/-- Equality of symmetric continuous multilinear maps is equivalent to equality on the diagonal. -/
theorem ext_iff_of_isSymm [CharZero 𝕜] [f.IsSymm] [g.IsSymm] :
    f = g ↔ ∀ x : E, f (fun _ => x) = g (fun _ => x) where
  mp h := by simp [h]
  mpr := ext_of_diagonal

end ContinuousMultilinearMap

namespace MultilinearMap

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {n : ℕ}
variable {f : MultilinearMap 𝕜 (fun _ : Fin n => E) F}

/-- An unbundled symmetric multilinear map which is continuous is zero if it vanishes on the
diagonal and `n!` is nonzero in the scalar field. -/
theorem eq_zero_of_diagonal_eq_zero_of_continuous_of_factorial_ne_zero [f.IsSymm]
    (hn : (n.factorial : 𝕜) ≠ 0) (hcont : Continuous f)
    (hdiag : ∀ x : E, f (fun _ => x) = 0) : f = 0 := by
  let fc : E [×n]→L[𝕜] F := ⟨f, hcont⟩
  have : fc.IsSymm := { domDomCongr_eq := IsSymm.domDomCongr_eq }
  have hc : fc = 0 :=
    fc.eq_zero_of_diagonal_eq_zero_of_factorial_ne_zero hn hdiag
  ext v
  change fc v = 0
  rw [hc]
  rfl

/-- A continuous symmetric multilinear map over a characteristic-zero nontrivially normed field
is zero if it vanishes on the diagonal. -/
theorem eq_zero_of_diagonal_eq_zero_of_continuous [CharZero 𝕜] [f.IsSymm]
    (hcont : Continuous f) (hdiag : ∀ x : E, f (fun _ => x) = 0) : f = 0 :=
  f.eq_zero_of_diagonal_eq_zero_of_continuous_of_factorial_ne_zero
    (Nat.cast_ne_zero.mpr n.factorial_ne_zero) hcont hdiag

end MultilinearMap
