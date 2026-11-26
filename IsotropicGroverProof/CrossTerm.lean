-- IsotropicGroverProof/CrossTerm.lean
-- Uniform probability measure perpSphereMeasure on the equatorial unit sphere V_perp Φ ∩ S^{d-1},
-- antipodal/isometry/Householder reflection symmetries, vanishing of the linear cross term,
-- and the expanded expectation formula expanded_E_pe.

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import IsotropicGroverProof.Composition

/-!
# Equatorial Sphere Measure, Reflection Symmetries, and Cross-Term Vanishing

Constructs the normalized uniform sphere measure `perpSphereMeasure Φ` on `V_perp Φ ∩ S^{d-1}`,
establishes antipodal invariance (`perpSphereMeasure_neg_invariant`), ambient linear-isometry
equivariance (`perpSphereMeasure_map_isometry`), orthogonal/Householder reflection symmetries
(`integral_perpSphere_inner_mul_ortho`, `integral_perpSphere_inner_sq_eq`), and derives
`E[p_e] = f₂ · p_ideal + (1 - f₂) · E[|⟨w|e₂⟩|²]` (`expanded_E_pe`).
-/

namespace IsotropicGrover

open MeasureTheory Real Metric InnerProductSpace

variable {n : ℕ}

/-! ## The perpendicular subspace V_perp = (ℝ · Φ)^⊥ -/

/-- The subspace of ℝ^d orthogonal to Φ. -/
noncomputable def V_perp (Φ : E n) : Submodule ℝ (E n) :=
  (Submodule.span ℝ {Φ})ᗮ

lemma mem_V_perp_iff (Φ v : E n) : v ∈ V_perp Φ ↔ inner (𝕜 := ℝ) Φ v = 0 := by
  simp only [V_perp, Submodule.mem_orthogonal, Submodule.mem_span_singleton]
  constructor
  · intro h
    have := h Φ ⟨1, one_smul ℝ Φ⟩
    simpa using this
  · intro h u hu
    obtain ⟨c, rfl⟩ := hu
    simp [inner_smul_left, h]

/-- V_perp is a closed subspace. -/
lemma V_perp_isClosed (Φ : E n) : IsClosed (V_perp Φ : Set (E n)) :=
  Submodule.isClosed_orthogonal _

/-- Negation maps V_perp to itself. -/
lemma neg_mem_V_perp (Φ v : E n) (hv : v ∈ V_perp Φ) : -v ∈ V_perp Φ :=
  (V_perp Φ).neg_mem hv

/-- Inner product with a negated vector. -/
lemma inner_neg_V_perp (û v : E n) :
    inner (𝕜 := ℝ) (-v) û = -inner (𝕜 := ℝ) v û :=
  inner_neg_left v û

/-! ## Uniform measure on the sphere of V_perp
    We model this as a Measure (E n) supported on {v | v ∈ V_perp Φ ∧ ‖v‖ = 1}. -/

lemma V_perp_finrank_pos (Φ : E n) : 0 < Module.finrank ℝ ↥(V_perp Φ) := by
  have hd := two_le_d n
  have horth := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E n)
    (Submodule.span ℝ {Φ})
  have hfin : Module.finrank ℝ (E n) = d n := by simp [E]
  have hspan : Module.finrank ℝ (Submodule.span ℝ {Φ} : Submodule ℝ (E n)) ≤ 1 :=
    (finrank_span_le_card ({Φ} : Set (E n))).trans (by simp)
  change 0 < Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n))ᗮ
  have h2 : Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n)) +
            Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n))ᗮ = d n := by
    linarith [horth]
  omega

private instance V_perp_nontrivial (Φ : E n) : Nontrivial ↥(V_perp Φ) :=
  Module.nontrivial_of_finrank_pos (V_perp_finrank_pos Φ)

-- The additive Haar measure on V_perp (using a let binding for BorelSpace
-- to work around an instance-synthesis limitation with noncomputable defs).
private noncomputable def V_perp_haar (Φ : E n) : Measure ↥(V_perp Φ) :=
  let hb : BorelSpace ↥(V_perp Φ) := inferInstance
  @Module.Basis.addHaar _ _ _ _ _ _ hb (stdOrthonormalBasis ℝ ↥(V_perp Φ)).toBasis

private lemma V_perp_haar_isAddHaar (Φ : E n) :
    Measure.IsAddHaarMeasure (V_perp_haar Φ) := by
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  exact @isAddHaarMeasure_basis_addHaar _ _ _ _ _ _ hb
      (stdOrthonormalBasis ℝ ↥(V_perp Φ)).toBasis

-- The uniform (unnormalized) sphere measure on the unit sphere of V_perp.
private noncomputable def V_perp_rawSph (Φ : E n) :
    Measure (Metric.sphere (0 : ↥(V_perp Φ)) 1) :=
  (V_perp_haar Φ).toSphere

private lemma V_perp_rawSph_ne_zero (Φ : E n) : V_perp_rawSph Φ ≠ 0 := by
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  have hhaar := V_perp_haar_isAddHaar Φ
  change (V_perp_haar Φ).toSphere ≠ 0
  exact @Measure.toSphere_ne_zero _ _ _ _ (V_perp_haar Φ) hb _ hhaar _

private lemma V_perp_rawSph_isFinite (Φ : E n) :
    IsFiniteMeasure (V_perp_rawSph Φ) := by
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  have hhaar := V_perp_haar_isAddHaar Φ
  change IsFiniteMeasure (V_perp_haar Φ).toSphere
  exact @Measure.instIsFiniteMeasureElemSphereOfNatRealToSphere _ _ _ _ (V_perp_haar Φ) hb _ hhaar

/-- The uniform probability measure on the unit sphere of V_perp, modeled as a
    measure on the ambient space E n supported on V_perp ∩ S^{d-1}. -/
noncomputable def perpSphereMeasure (Φ : E n) : Measure (E n) :=
  let rawSph := V_perp_rawSph Φ
  let totalMass := rawSph Set.univ
  let toEn := fun (x : Metric.sphere (0 : ↥(V_perp Φ)) 1) =>
      ((x.val : ↥(V_perp Φ)) : E n)
  (totalMass⁻¹ • rawSph).map toEn

/-- The perpSphereMeasure is a probability measure. -/
instance perpSphereMeasure_isProbMeasure (Φ : E n) :
    IsProbabilityMeasure (perpSphereMeasure Φ) := by
  have htoEn_meas : Measurable
      (fun x : Metric.sphere (0 : ↥(V_perp Φ)) 1 => ((x.val : ↥(V_perp Φ)) : E n)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have hrawSph_ne_zero : V_perp_rawSph Φ ≠ 0 := V_perp_rawSph_ne_zero Φ
  have htotalMass_ne_zero : (V_perp_rawSph Φ) Set.univ ≠ 0 := by
    intro h; exact hrawSph_ne_zero (Measure.measure_univ_eq_zero.mp h)
  have htotalMass_ne_top : (V_perp_rawSph Φ) Set.univ ≠ ⊤ := by
    have := V_perp_rawSph_isFinite Φ; exact (measure_lt_top _ _).ne
  constructor
  show perpSphereMeasure Φ Set.univ = 1
  simp only [perpSphereMeasure]
  rw [Measure.map_apply htoEn_meas MeasurableSet.univ, Set.preimage_univ,
      Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel htotalMass_ne_zero htotalMass_ne_top

/-- Almost all e₂ w.r.t. perpSphereMeasure lie in V_perp Φ with unit norm. -/
lemma perpSphereMeasure_norm_ae (Φ : E n) :
    ∀ᵐ e₂ ∂(perpSphereMeasure Φ), e₂ ∈ V_perp Φ ∧ ‖e₂‖ = 1 := by
  have htoEn_meas : Measurable
      (fun x : Metric.sphere (0 : ↥(V_perp Φ)) 1 => ((x.val : ↥(V_perp Φ)) : E n)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have := V_perp_rawSph_isFinite Φ
  have htotalMass_inv_ne_zero : (V_perp_rawSph Φ Set.univ)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (measure_lt_top _ _).ne
  simp only [perpSphereMeasure]
  have hmeasSet : MeasurableSet {e₂ : E n | e₂ ∈ V_perp Φ ∧ ‖e₂‖ = 1} := by
    have hV : MeasurableSet (V_perp Φ : Set (E n)) := (V_perp_isClosed Φ).measurableSet
    have hS : MeasurableSet (Metric.sphere (0 : E n) 1) := isClosed_sphere.measurableSet
    convert hV.inter hS using 1
    ext e₂; simp
  rw [ae_map_iff htoEn_meas.aemeasurable hmeasSet,
      Measure.ae_ennreal_smul_measure_iff htotalMass_inv_ne_zero]
  apply ae_of_all
  intro ⟨x, hx⟩
  have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  constructor
  · exact x.property
  · rw [Submodule.norm_coe]; exact hx'

-- Helper: V_perp Haar measure is invariant under linear isometries of V_perp.
private lemma V_perp_haar_map_isometry (Φ : E n)
    (f : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ)) :
    Measure.map f (V_perp_haar Φ) = V_perp_haar Φ := by
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  have hhaar : Measure.IsAddHaarMeasure (V_perp_haar Φ) := V_perp_haar_isAddHaar Φ
  let g : ↥(V_perp Φ) →ₗ[ℝ] ↥(V_perp Φ) := f.toLinearEquiv.toLinearMap
  have hfg : (f : ↥(V_perp Φ) → ↥(V_perp Φ)) = g := rfl
  have hdet : g.det ≠ 0 := f.toLinearEquiv.isUnit_det'.ne_zero
  rw [hfg, @Measure.map_linearMap_addHaar_eq_smul_addHaar
      ↥(V_perp Φ) _ _ _ hb _ (V_perp_haar Φ) hhaar g hdet]
  suffices h : |g.det| = 1 by simp [abs_inv, h]
  -- det of a linear isometry is ±1: use OrthonormalBasis.det_to_matrix_orthonormalBasis_real
  let b := stdOrthonormalBasis ℝ ↥(V_perp Φ)
  have hdet_eq : g.det = b.toBasis.det (b.map f) := by
    have h1 : (b.map f : Fin _ → ↥(V_perp Φ)) = g ∘ ⇑b.toBasis := by
      ext i; simp [g, b, OrthonormalBasis.map]
    rw [h1, b.toBasis.det_comp g ⇑b.toBasis, b.toBasis.det_self, mul_one]
  have hpm := b.det_to_matrix_orthonormalBasis_real (b.map f)
  rcases hpm with h | h <;> simp [hdet_eq, h]

-- Helper: push `V_perp_rawSph` forward along an isometry equivalence preserving `V_perp_haar`.
private lemma V_perp_rawSph_map_equiv {Φ₁ Φ₂ : E n}
    (f : ↥(V_perp Φ₁) ≃ₗᵢ[ℝ] ↥(V_perp Φ₂))
    (hhaar : Measure.map f (V_perp_haar Φ₁) = V_perp_haar Φ₂) :
    let fSph : Metric.sphere (0 : ↥(V_perp Φ₁)) 1 → Metric.sphere (0 : ↥(V_perp Φ₂)) 1 :=
      fun x => ⟨f x.val,
        mem_sphere_zero_iff_norm.mpr (by rw [f.norm_map]; exact norm_eq_of_mem_sphere x)⟩
    Measure.map fSph (V_perp_rawSph Φ₁) = V_perp_rawSph Φ₂ := by
  intro fSph
  have hb₁ : BorelSpace ↥(V_perp Φ₁) := inferInstance
  have hb₂ : BorelSpace ↥(V_perp Φ₂) := inferInstance
  have hfSph_meas : Measurable fSph :=
    ((f.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hf_meas : Measurable (f : ↥(V_perp Φ₁) → ↥(V_perp Φ₂)) :=
    @Continuous.measurable _ _ _ _ (@BorelSpace.opensMeasurable _ _ _ hb₁) _ _ hb₂
      (f : ↥(V_perp Φ₁) → ↥(V_perp Φ₂)) f.continuous
  have hf_symm_meas : Measurable (f.symm : ↥(V_perp Φ₂) → ↥(V_perp Φ₁)) :=
    @Continuous.measurable _ _ _ _ (@BorelSpace.opensMeasurable _ _ _ hb₂) _ _ hb₁
      (f.symm : ↥(V_perp Φ₂) → ↥(V_perp Φ₁)) f.symm.continuous
  have hmembed : MeasurableEmbedding (f : ↥(V_perp Φ₁) → ↥(V_perp Φ₂)) :=
    ⟨f.injective, hf_meas, fun {s} hs => by
      rw [Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply]
      exact hf_symm_meas hs⟩
  ext s hs
  simp only [V_perp_rawSph, Measure.map_apply hfSph_meas hs]
  rw [@Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ₁) hb₁ _ (hs.preimage hfSph_meas),
      @Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ₂) hb₂ _ hs,
      f.toLinearEquiv.finrank_eq]
  congr 1
  suffices hsets : ∀ (T₁ : Set ↥(V_perp Φ₁)) (T₂ : Set ↥(V_perp Φ₂)),
      T₁ = f ⁻¹' T₂ → (V_perp_haar Φ₁) T₁ = (V_perp_haar Φ₂) T₂ by
    apply hsets
    ext y
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, v, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, (fSph z).val, ⟨fSph z, hz, rfl⟩, by simp [fSph, map_smul]⟩
    · rintro ⟨r, hr, v, ⟨x, hxs, rfl⟩, h⟩
      let w : Metric.sphere (0 : ↥(V_perp Φ₁)) 1 :=
        ⟨f.symm x.val, mem_sphere_zero_iff_norm.mpr
          (by rw [f.symm.norm_map]; exact norm_eq_of_mem_sphere x)⟩
      refine ⟨r, hr, w.val, ⟨w, ?_, rfl⟩, ?_⟩
      · simp only [Set.mem_preimage]
        convert hxs using 1
        ext; simp [fSph, w, f.apply_symm_apply]
      · have h1 := f.symm_apply_apply y
        rw [← h, map_smul] at h1
        exact h1
  intro T₁ T₂ hT
  rw [hT, ← hmembed.map_apply (V_perp_haar Φ₁), hhaar]

-- Helper: the raw sphere measure is invariant under linear isometries of V_perp.
private lemma V_perp_rawSph_isometry_invariant (Φ : E n)
    (f : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ)) :
    let fSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
      fun x => ⟨f x.val,
        mem_sphere_zero_iff_norm.mpr (by rw [f.norm_map]; exact norm_eq_of_mem_sphere x)⟩
    Measure.map fSph (V_perp_rawSph Φ) = V_perp_rawSph Φ :=
  V_perp_rawSph_map_equiv f (V_perp_haar_map_isometry Φ f)

/-- The perpSphereMeasure is invariant under negation (antipodal symmetry). -/
lemma perpSphereMeasure_neg_invariant (Φ : E n) :
    Measure.map Neg.neg (perpSphereMeasure Φ) = perpSphereMeasure Φ := by
  simp only [perpSphereMeasure]
  set rawSph := V_perp_rawSph Φ
  set toEn := fun (x : Metric.sphere (0 : ↥(V_perp Φ)) 1) =>
      ((x.val : ↥(V_perp Φ)) : E n)
  have htoEn_meas : Measurable toEn :=
    measurable_subtype_coe.comp measurable_subtype_coe
  let negIso : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ) := LinearIsometryEquiv.neg ℝ
  let negSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
    fun x => ⟨negIso x.val,
      mem_sphere_zero_iff_norm.mpr (by rw [negIso.norm_map]; exact norm_eq_of_mem_sphere x)⟩
  have hnegSph_meas : Measurable negSph :=
    ((negIso.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hcomm : (Neg.neg : E n → E n) ∘ toEn = toEn ∘ negSph := by
    ext x; simp [Function.comp, toEn, negSph, negIso]
  rw [Measure.map_map measurable_neg htoEn_meas, hcomm,
      ← Measure.map_map htoEn_meas hnegSph_meas,
      Measure.map_smul _ hnegSph_meas.aemeasurable,
      V_perp_rawSph_isometry_invariant Φ negIso]

/-- Pushing `perpSphereMeasure Φ` forward by an ambient linear isometry `L` yields
    `perpSphereMeasure (L Φ)`. -/
lemma perpSphereMeasure_map_isometry (Φ : E n) (L : E n ≃ₗᵢ[ℝ] E n) :
    Measure.map L (perpSphereMeasure Φ) = perpSphereMeasure (L Φ) := by
  have hb₁ : BorelSpace ↥(V_perp Φ) := inferInstance
  have hb₂ : BorelSpace ↥(V_perp (L Φ)) := inferInstance
  let L_perp : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp (L Φ)) :=
    { toFun := fun v => ⟨L v.val, (mem_V_perp_iff (L Φ) (L v.val)).mpr
        (by rw [L.inner_map_map]; exact (mem_V_perp_iff Φ v.val).mp v.property)⟩
      invFun := fun w => ⟨L.symm w.val, (mem_V_perp_iff Φ (L.symm w.val)).mpr
        (by rw [← L.inner_map_map, L.apply_symm_apply]
            exact (mem_V_perp_iff (L Φ) w.val).mp w.property)⟩
      map_add' := fun u v => Subtype.ext (map_add L u.val v.val)
      map_smul' := fun c v => Subtype.ext (map_smul L c v.val)
      left_inv := fun v => Subtype.ext (L.symm_apply_apply v.val)
      right_inv := fun w => Subtype.ext (L.apply_symm_apply w.val)
      norm_map' := fun v => L.norm_map v.val }
  have hhaar_eq : Measure.map L_perp (V_perp_haar Φ) = V_perp_haar (L Φ) := by
    let b₁ := stdOrthonormalBasis ℝ ↥(V_perp Φ)
    let b₂ := stdOrthonormalBasis ℝ ↥(V_perp (L Φ))
    let eIdx := finCongr L_perp.toLinearEquiv.finrank_eq
    let b₁' := (b₁.map L_perp).reindex eIdx
    let M : ↥(V_perp (L Φ)) ≃ₗᵢ[ℝ] ↥(V_perp (L Φ)) := b₂.repr.trans b₁'.repr.symm
    have hM_haar : Measure.map M (V_perp_haar (L Φ)) = V_perp_haar (L Φ) :=
      V_perp_haar_map_isometry (L Φ) M
    have hmap1 : Measure.map L_perp (V_perp_haar Φ) =
        @Module.Basis.addHaar _ _ _ _ _ _ hb₂
          (b₁.toBasis.map L_perp.toContinuousLinearEquiv.toLinearEquiv) := by
      simpa [V_perp_haar, b₁] using
        @Module.Basis.map_addHaar _ _ _ _ _ _ _ _ _ _ hb₁ hb₂ _ _
          b₁.toBasis L_perp.toContinuousLinearEquiv
    have hmap2 : Measure.map M (V_perp_haar (L Φ)) =
        @Module.Basis.addHaar _ _ _ _ _ _ hb₂
          (b₂.toBasis.map M.toContinuousLinearEquiv.toLinearEquiv) := by
      simpa [V_perp_haar, b₂] using
        @Module.Basis.map_addHaar _ _ _ _ _ _ _ _ _ _ hb₂ hb₂ _ _
          b₂.toBasis M.toContinuousLinearEquiv
    have hbasis_eq : b₂.toBasis.map M.toContinuousLinearEquiv.toLinearEquiv = b₁'.toBasis := by
      ext i
      simp [M]
    have hb₁'_toBasis : b₁'.toBasis =
        (b₁.toBasis.map L_perp.toContinuousLinearEquiv.toLinearEquiv).reindex eIdx := by
      ext i
      simp [b₁']
    rw [hmap1, ← @Module.Basis.addHaar_reindex _ _ _ _ _ _ _ _ hb₂
      (b₁.toBasis.map L_perp.toContinuousLinearEquiv.toLinearEquiv) eIdx,
      ← hb₁'_toBasis, ← hbasis_eq, ← hmap2, hM_haar]
  let fSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp (L Φ))) 1 :=
    fun x => ⟨L_perp x.val,
      mem_sphere_zero_iff_norm.mpr (by rw [L_perp.norm_map]; exact norm_eq_of_mem_sphere x)⟩
  have hfSph_meas : Measurable fSph :=
    ((L_perp.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hrawSph_eq : Measure.map fSph (V_perp_rawSph Φ) = V_perp_rawSph (L Φ) :=
    V_perp_rawSph_map_equiv L_perp hhaar_eq
  simp only [perpSphereMeasure]
  set rawSph₁ := V_perp_rawSph Φ
  set rawSph₂ := V_perp_rawSph (L Φ)
  set toEn₁ := fun (x : Metric.sphere (0 : ↥(V_perp Φ)) 1) => ((x.val : ↥(V_perp Φ)) : E n)
  set toEn₂ := fun (x : Metric.sphere (0 : ↥(V_perp (L Φ))) 1) => ((x.val : ↥(V_perp (L Φ))) : E n)
  have htoEn₁_meas : Measurable toEn₁ := measurable_subtype_coe.comp measurable_subtype_coe
  have htoEn₂_meas : Measurable toEn₂ := measurable_subtype_coe.comp measurable_subtype_coe
  have hcomm : (L : E n → E n) ∘ toEn₁ = toEn₂ ∘ fSph := by
    ext x; rfl
  have hmass : rawSph₂ Set.univ = rawSph₁ Set.univ := by
    rw [← hrawSph_eq, Measure.map_apply hfSph_meas MeasurableSet.univ, Set.preimage_univ]
  rw [hmass, Measure.map_map L.continuous.measurable htoEn₁_meas, hcomm,
      ← Measure.map_map htoEn₂_meas hfSph_meas,
      Measure.map_smul _ hfSph_meas.aemeasurable, hrawSph_eq]

/-! ## Integrability of inner products over perpSphereMeasure -/

/-- Inner product ⟨e₂, y⟩ is integrable over perpSphereMeasure.
    Proof sketch: |⟨e₂, y⟩| ≤ ‖y‖ on the unit sphere (Cauchy–Schwarz),
    and perpSphereMeasure is a finite measure. -/
lemma inner_integrable (Φ y : E n) :
    Integrable (fun e₂ => inner (𝕜 := ℝ) e₂ y) (perpSphereMeasure Φ) := by
  apply Integrable.mono' (integrable_const ‖y‖)
  · exact (continuous_id.inner continuous_const (𝕜 := ℝ)).aestronglyMeasurable
  · filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨_, he₂⟩
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) e₂ y|
        ≤ ‖e₂‖ * ‖y‖ := abs_real_inner_le_norm e₂ y
      _ = 1 * ‖y‖   := by rw [he₂]
      _ = ‖y‖       := one_mul _

/-- succProb n e₂ w is integrable over perpSphereMeasure.
    Proof sketch: succProb is continuous (sum of squares of inner products),
    and perpSphereMeasure is supported on the compact unit sphere. -/
lemma succProb_integrable (Φ : E n) (w : Fin (2 ^ n)) :
    Integrable (fun e₂ => succProb n e₂ w) (perpSphereMeasure Φ) := by
  apply Integrable.mono' (integrable_const (2 : ℝ))
  · apply Continuous.aestronglyMeasurable
    simp only [succProb]
    exact (((continuous_id.inner continuous_const (𝕜 := ℝ)).pow 2).add
           ((continuous_id.inner continuous_const (𝕜 := ℝ)).pow 2))
  · filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨_, he₂⟩
    simp only [Real.norm_eq_abs, succProb]
    have hnn : 0 ≤ inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) ^ 2 +
                   inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [abs_of_nonneg hnn]
    have bound : ∀ û : E n, ‖û‖ = 1 → inner (𝕜 := ℝ) e₂ û ^ 2 ≤ 1 := by
      intro û hû
      have h := abs_real_inner_le_norm e₂ û
      rw [he₂, hû, mul_one] at h
      have := sq_abs (inner (𝕜 := ℝ) e₂ û)
      nlinarith [abs_nonneg (inner (𝕜 := ℝ) e₂ û)]
    linarith [bound (stdBasisVec n (succProbIdx0 n w)) (stdBasisVec_norm n _),
              bound (stdBasisVec n (succProbIdx1 n w)) (stdBasisVec_norm n _),
              sq_nonneg (inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w))),
              sq_nonneg (inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))]

/-! ## Algebraic expansion of succProb(isotropicError Φ e₂ θ) -/

/-- Expand succProb(cosθ·Φ + sinθ·e₂, w) into three terms via bilinearity. -/
lemma succProb_isotropicError_expand (Φ e₂ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    succProb n (isotropicError Φ e₂ θ) w =
    cos θ ^ 2 * succProb n Φ w +
    2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
                         inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) +
    sin θ ^ 2 * succProb n e₂ w := by
  simp only [succProb, isotropicError, inner_add_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-! ## E[e₂] = 0 by antipodal symmetry -/

/-- The inner product ⟨e₂, û⟩ has zero expectation for any fixed û.
    Proof: the antipodal map e₂ ↦ -e₂ is measure-preserving on perpSphereMeasure
    and negates ⟨e₂, û⟩, so ∫ ⟨e₂, û⟩ = -∫ ⟨e₂, û⟩ = 0. -/
lemma integral_perp_inner_eq_zero (Φ û : E n) :
    ∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ) = 0 := by
  have hmeas : MeasurePreserving Neg.neg (perpSphereMeasure Φ) (perpSphereMeasure Φ) :=
    ⟨measurable_neg, perpSphereMeasure_neg_invariant Φ⟩
  have heq : ∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ) =
             -(∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ)) := by
    conv_lhs => rw [← hmeas.integral_comp measurableEmbedding_neg
                       (fun e₂ => inner (𝕜 := ℝ) e₂ û)]
    simp_rw [inner_neg_left, integral_neg]
  linarith

/-- The cross term (a linear function of e₂) integrates to zero. -/
lemma integral_cross_term_eq_zero (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    ∫ e₂, 2 * cos θ * sin θ *
          (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
           inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))
    ∂(perpSphereMeasure Φ) = 0 := by
  have key0 := integral_perp_inner_eq_zero Φ (stdBasisVec n (succProbIdx0 n w))
  have key1 := integral_perp_inner_eq_zero Φ (stdBasisVec n (succProbIdx1 n w))
  have hsimp : (fun e₂ : E n => 2 * cos θ * sin θ *
          (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
           inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) =
       (fun e₂ => 2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner ℝ e₂ (stdBasisVec n (succProbIdx0 n w)) +
         2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner ℝ e₂ (stdBasisVec n (succProbIdx1 n w))) := by ext; ring
  rw [hsimp, integral_add ((inner_integrable Φ _).const_mul _) ((inner_integrable Φ _).const_mul _),
      integral_const_mul, integral_const_mul, key0, key1, mul_zero, mul_zero, add_zero]

/-- The cross term function is integrable. -/
lemma cross_integrable (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    Integrable (fun e₂ : E n => 2 * cos θ * sin θ *
      (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) (perpSphereMeasure Φ) := by
  have : (fun e₂ : E n => 2 * cos θ * sin θ *
      (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) = fun e₂ =>
    (2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx0 n w))) *
      inner ℝ e₂ (stdBasisVec n (succProbIdx0 n w)) +
    (2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx1 n w))) *
      inner ℝ e₂ (stdBasisVec n (succProbIdx1 n w)) := by ext; ring
  rw [this]
  exact ((inner_integrable Φ _).const_mul _).add ((inner_integrable Φ _).const_mul _)

/-! ## Inner integral over e₂ -/

/-- After integrating over e₂, the cross term vanishes:
    ∫ e₂, succProb(cosθ·Φ + sinθ·e₂, w) = cos²θ · p_Φ + sin²θ · ∫ e₂, p_{e₂} -/
lemma integral_e₂_succProb (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    ∫ e₂, succProb n (isotropicError Φ e₂ θ) w ∂(perpSphereMeasure Φ) =
    cos θ ^ 2 * succProb n Φ w +
    sin θ ^ 2 * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ) := by
  have hf1 : Integrable (fun _ : E n => cos θ ^ 2 * succProb n Φ w) (perpSphereMeasure Φ) :=
    integrable_const _
  have hf2 := cross_integrable Φ θ w
  have hf3 : Integrable (fun e₂ => sin θ ^ 2 * succProb n e₂ w) (perpSphereMeasure Φ) :=
    (succProb_integrable Φ w).const_mul _
  -- Explicit beta-reduced type for hf1+hf2, so rw [integral_add hf12 hf3] can match
  have hf12 : Integrable (fun e₂ : E n => cos θ ^ 2 * succProb n Φ w +
      2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
        inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
        inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
        inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) (perpSphereMeasure Φ) :=
    hf1.add hf2
  -- Rewrite integrand pointwise (under the binder) using the algebraic expansion
  simp_rw [succProb_isotropicError_expand Φ _ θ w]
  -- step1: ∫(A + cross) = A (cross integrates to 0, constant has measure 1)
  have step1 : ∫ e₂ : E n, cos θ ^ 2 * succProb n Φ w +
      2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) ∂perpSphereMeasure Φ =
      cos θ ^ 2 * succProb n Φ w := by
    rw [integral_add hf1 hf2, integral_const, integral_cross_term_eq_zero]
    simp -- closes ENNReal.toReal 1 • A + 0 = A via IsProbabilityMeasure
  rw [integral_add hf12 hf3, step1, integral_const_mul]

/-! ## Expanded expectation E[p_e] -/

/-- The expected success probability expands as:
    E[p_e] = f₂ · p_ideal + (1 - f₂) · E[|⟨w|e₂⟩|²]
    Proof sketch:
    1. Expand succProb via succProb_isotropicError_expand
    2. Integrate over e₂ using integral_e₂_succProb (cross term = 0)
    3. Integrate over θ: ∫cos²θ dθ = f₂, ∫sin²θ dθ = 1 - f₂ (from isProbMeasure + f₂ def)
    4. Collect terms -/
theorem expanded_E_pe (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (_hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ) ∂(composedMeasure (d n) G σ) =
    f₂ (d n) G σ * succProb n Φ w +
    (1 - f₂ (d n) G σ) * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ) := by
  have : IsProbabilityMeasure (composedMeasure (d n) G σ) :=
    composedMeasure_isProbMeasure (d n) G σ hσ hG (two_le_d n)
  simp_rw [integral_e₂_succProb Φ _ w]
  -- Goal: ∫ θ, (cos²θ · p + sin²θ · q) ∂μ = f₂·p + (1-f₂)·q
  -- where f₂ = ∫ cos²θ ∂μ definitionally
  set μ := composedMeasure (d n) G σ
  have hcos_int : Integrable (fun θ => cos θ ^ 2) μ := cos_sq_integrable_prob
  have hsin_int : Integrable (fun θ => sin θ ^ 2) μ := sin_sq_integrable_prob
  have hf₂_def : f₂ (d n) G σ = ∫ θ, cos θ ^ 2 ∂μ := rfl
  have hsin_f₂ : ∫ θ, sin θ ^ 2 ∂μ = 1 - f₂ (d n) G σ := by
    have hsum : ∫ θ, (cos θ ^ 2 + sin θ ^ 2) ∂μ = 1 := by
      simp_rw [Real.cos_sq_add_sin_sq]
      simp
    rw [integral_add hcos_int hsin_int] at hsum
    linarith [hf₂_def]
  rw [integral_add (hcos_int.mul_const _) (hsin_int.mul_const _),
      integral_mul_const, integral_mul_const, hsin_f₂, ← hf₂_def]

/-! ## Isometry invariance helpers for the Schur argument -/

private lemma integral_perpSphere_reflection_eq (Φ : E n) {w : E n}
    (hw : ⟪Φ, w⟫_ℝ = 0) {g : E n → ℝ} :
    ∫ e₂, g ((Submodule.span ℝ {w})ᗮ.reflection e₂) ∂(perpSphereMeasure Φ) =
    ∫ e₂, g e₂ ∂(perpSphereMeasure Φ) := by
  let K : Submodule ℝ (E n) := (Submodule.span ℝ {w})ᗮ
  let R : E n ≃ₗᵢ[ℝ] E n := K.reflection
  have hΦK : Φ ∈ K :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hw
  have hRΦ : R Φ = Φ := Submodule.reflection_mem_subspace_eq_self hΦK
  have hmp : MeasurePreserving R (perpSphereMeasure Φ) (perpSphereMeasure Φ) :=
    ⟨R.continuous.measurable, by rw [perpSphereMeasure_map_isometry, hRΦ]⟩
  exact hmp.integral_comp R.toHomeomorph.measurableEmbedding g

/-- Off-diagonal vanishing: for orthogonal u, v ∈ V_perp, ∫ ⟨e₂,u⟩⟨e₂,v⟩ dμ = 0.
    Uses reflection in (span{u})ᗮ fixing Φ: the reflection negates the u-component
    and preserves the v-component, while the sphere measure is invariant. -/
lemma integral_perpSphere_inner_mul_ortho (Φ : E n)
    (u v : ↥(V_perp Φ)) (huv : ⟪(u : E n), (v : E n)⟫_ℝ = 0) :
    ∫ e₂, ⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ ∂(perpSphereMeasure Φ) = 0 := by
  let K : Submodule ℝ (E n) := (Submodule.span ℝ {(u : E n)})ᗮ
  have huΦ : ⟪Φ, (u : E n)⟫_ℝ = 0 := (mem_V_perp_iff Φ u).mp u.2
  have hvK : (v : E n) ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm]
    exact huv
  have hsym : ∫ e₂, ⟪K.reflection e₂, (u : E n)⟫_ℝ * ⟪K.reflection e₂, (v : E n)⟫_ℝ
      ∂(perpSphereMeasure Φ) =
      ∫ e₂, ⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ ∂(perpSphereMeasure Φ) :=
    integral_perpSphere_reflection_eq Φ huΦ
      (g := fun e₂ => ⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ)
  have hterm : ∀ e₂ : E n,
      ⟪K.reflection e₂, (u : E n)⟫_ℝ * ⟪K.reflection e₂, (v : E n)⟫_ℝ =
      -(⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ) := fun e₂ => by
    have hadj : ∀ y : E n, ⟪K.reflection e₂, y⟫_ℝ = ⟪e₂, K.reflection y⟫_ℝ := fun y => by
      simpa using K.reflection.inner_map_map e₂ (K.reflection y)
    rw [hadj, hadj, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
        Submodule.reflection_mem_subspace_eq_self hvK, inner_neg_right, neg_mul]
  simp_rw [hterm] at hsym
  rw [integral_neg] at hsym
  linarith

/-- Diagonal equality: for unit u, v ∈ V_perp, ∫ ⟨e₂,u⟩² = ∫ ⟨e₂,v⟩².
    Uses Householder reflection (span{u-v})ᗮ fixing Φ, which maps
    u ↦ v (by reflection_sub) while leaving perpSphereMeasure invariant. -/
lemma integral_perpSphere_inner_sq_eq (Φ : E n)
    (u v : ↥(V_perp Φ)) (hu : ‖(u : E n)‖ = 1)
    (hv : ‖(v : E n)‖ = 1) :
    ∫ e₂, ⟪e₂, (u : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
    ∫ e₂, ⟪e₂, (v : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) := by
  let K : Submodule ℝ (E n) := (Submodule.span ℝ {(u : E n) - (v : E n)})ᗮ
  have hsubΦ : ⟪Φ, (u : E n) - (v : E n)⟫_ℝ = 0 :=
    (mem_V_perp_iff Φ _).mp ((V_perp Φ).sub_mem u.2 v.2)
  rw [← integral_perpSphere_reflection_eq Φ hsubΦ (g := fun e₂ => ⟪e₂, (u : E n)⟫_ℝ ^ 2)]
  congr 1; ext e₂
  have hadj : ⟪K.reflection e₂, (u : E n)⟫_ℝ = ⟪e₂, K.reflection (u : E n)⟫_ℝ := by
    simpa using K.reflection.inner_map_map e₂ (K.reflection (u : E n))
  rw [hadj, Submodule.reflection_sub (hu.trans hv.symm)]

/-! ## TDD spot-checks -/

-- V_perp contains vectors orthogonal to Φ
example (i j : Fin (d n)) (hij : i ≠ j) :
    stdBasisVec n j ∈ V_perp (stdBasisVec n i) := by
  rw [mem_V_perp_iff, inner_stdBasisVec, ite_eq_right hij]

-- Negation stays in V_perp
example (Φ v : E n) (hv : v ∈ V_perp Φ) : -v ∈ V_perp Φ :=
  Submodule.neg_mem _ hv

-- The algebraic expansion holds pointwise
example (Φ e₂ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    succProb n (isotropicError Φ e₂ θ) w =
    cos θ ^ 2 * succProb n Φ w +
    2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
                         inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) +
    sin θ ^ 2 * succProb n e₂ w :=
  succProb_isotropicError_expand Φ e₂ θ w

#check @perpSphereMeasure_map_isometry

/--
info: 'IsotropicGrover.perpSphereMeasure_map_isometry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms perpSphereMeasure_map_isometry

/--
info: 'IsotropicGrover.expanded_E_pe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms expanded_E_pe

end IsotropicGrover
