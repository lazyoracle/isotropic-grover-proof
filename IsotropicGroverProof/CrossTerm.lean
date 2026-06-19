-- IsotropicGroverProof/CrossTerm.lean
-- M4: The cross term in E[p_e] vanishes because E[e₂] = 0.
--     Derives the expanded form: E[p_e] = f₂ · p_ideal + (1-f₂) · E[|⟨w|e₂⟩|²]
--
-- SORRY BUDGET: 0 (fully proved)
--   PROVED (perpSphereMeasure_neg_invariant): antipodal symmetry of sphere measure

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import IsotropicGroverProof.Composition

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

private lemma V_perp_finrank_pos (Φ : E n) : 0 < Module.finrank ℝ ↥(V_perp Φ) := by
  have hd : 2 ≤ d n := by simp [d]; linarith [Nat.one_le_two_pow (n := n)]
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
    haveI := V_perp_rawSph_isFinite Φ; exact (measure_lt_top _ _).ne
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
  haveI := V_perp_rawSph_isFinite Φ
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

-- Helper: the Haar measure on V_perp is invariant under negation.
private lemma V_perp_haar_neg_invariant (Φ : E n) :
    Measure.map Neg.neg (V_perp_haar Φ) = V_perp_haar Φ := by
  -- Negation is the linear map (-1 : ℝ) • id, with det = (-1)^finrank, |det^{-1}| = 1
  -- We use the BorelSpace instance explicitly (as in V_perp_haar_isAddHaar)
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  have hhaar : Measure.IsAddHaarMeasure (V_perp_haar Φ) := V_perp_haar_isAddHaar Φ
  -- The negation linear map and its det
  let f : ↥(V_perp Φ) →ₗ[ℝ] ↥(V_perp Φ) := (-1 : ℝ) • LinearMap.id
  have hfneg : (f : ↥(V_perp Φ) → ↥(V_perp Φ)) = Neg.neg := by ext x; simp [f]
  have hdet : LinearMap.det f ≠ 0 := by
    simp only [f, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (by norm_num)
  rw [← hfneg, @Measure.map_linearMap_addHaar_eq_smul_addHaar
      ↥(V_perp Φ) _ _ _ hb _ (V_perp_haar Φ) hhaar f hdet]
  -- Goal: ENNReal.ofReal |(det f)^{-1}| • V_perp_haar Φ = V_perp_haar Φ
  -- det f = (-1)^finrank, |(-1)^finrank|⁻¹ = 1⁻¹ = 1
  simp only [f, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_inv,
             abs_neg_one_pow, inv_one, ENNReal.ofReal_one, one_smul]

-- Helper: the raw sphere measure on V_perp is invariant under negation.
-- We define negSph explicitly to avoid the InvolutiveNeg instance synthesis issue
-- (caused by a zero-instance diamond on submodule subtypes).
private lemma V_perp_rawSph_neg_invariant (Φ : E n) :
    let negSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
      fun x => ⟨-x.val,
        mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact norm_eq_of_mem_sphere x)⟩
    Measure.map negSph (V_perp_rawSph Φ) = V_perp_rawSph Φ := by
  intro negSph
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  -- negSph is measurable (it's continuous)
  have hnegSph_meas : Measurable negSph :=
    ((continuous_neg.comp continuous_subtype_val).subtype_mk _).measurable
  -- negation on V_perp is a measurable embedding (for MeasurableEmbedding.map_apply)
  have hmembed : MeasurableEmbedding (Neg.neg : ↥(V_perp Φ) → ↥(V_perp Φ)) :=
    measurableEmbedding_neg
  -- Change to a form where rw [toSphere_apply'] works without instance mismatch
  -- by restating the goal in terms of the explicit @-applied toSphere
  suffices h : ∀ (t : Set (Metric.sphere (0 : ↥(V_perp Φ)) 1)),
      MeasurableSet t →
      @Measure.toSphere _ _ _ _ (V_perp_haar Φ) (negSph ⁻¹' t) =
      @Measure.toSphere _ _ _ _ (V_perp_haar Φ) t by
    ext s hs
    simp only [V_perp_rawSph, Measure.map_apply hnegSph_meas hs]
    exact h s hs
  intro s hs
  -- Now use toSphere_apply' with explicit hb
  rw [@Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ) hb _ (hs.preimage hnegSph_meas),
      @Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ) hb _ hs]
  -- Goal: dim * μ(Ioo • ↑'' (negSph ⁻¹' s)) = dim * μ(Ioo • ↑'' s)
  -- Step 1: ↑'' (negSph ⁻¹' s) = -(↑'' s) [himg]
  -- Step 2: Ioo 0 1 • -(↑'' s) = -(Ioo 0 1 • ↑'' s) [smul_neg]
  -- Step 3: μ(-(Ioo • ↑'' s)) = μ(Ioo • ↑'' s) [neg-invariance]
  congr 1
  -- Goal: (V_perp_haar Φ) (Ioo 0 1 • val'' (negSph ⁻¹' s)) = (V_perp_haar Φ) (Ioo 0 1 • val'' s)
  -- Strategy: rewrite LHS as (map Neg.neg (V_perp_haar Φ)) (Ioo • val'' s) via set equality,
  -- then use V_perp_haar_neg_invariant.
  have hinv := V_perp_haar_neg_invariant Φ
  -- Rewrite using neg-invariance: sufficient to show the set arguments are equal
  -- in the form needed by hmembed.map_apply.
  -- We convert: (V_perp_haar Φ) (Ioo • val'' (negSph ⁻¹' s))
  --           = (V_perp_haar Φ) (Neg.neg ⁻¹' (Ioo • val'' s))
  -- because Ioo • val'' (negSph ⁻¹' s) = Neg.neg ⁻¹' (Ioo • val'' s)
  -- (element membership: y = r • (-x.val) ↔ -y = r • x.val)
  -- Then use ← hmembed.map_apply + hinv.
  -- We avoid stating the set equality as a `have` (which requires spelling out the set type
  -- and causes HSMul (Set ℝ) (Set ↥(V_perp Φ)) synthesis failure).
  -- Instead, use congr_arg with a suffices.
  suffices hsets : ∀ (T₁ T₂ : Set ↥(V_perp Φ)),
      T₁ = Neg.neg ⁻¹' T₂ → (V_perp_haar Φ) T₁ = (V_perp_haar Φ) T₂ by
    apply hsets
    -- Goal: Ioo • val'' (negSph ⁻¹' s) = Neg.neg ⁻¹' (Ioo • val'' s)
    -- (y is in the LHS iff -y ∈ Ioo • val'' s)
    ext y
    simp only [Set.mem_preimage]
    constructor
    · -- Forward: y = r • v where v ∈ val'' (negSph ⁻¹' s)
      --   → ∃ z ∈ sphere with z ∈ negSph ⁻¹' s and v = z.val, y = r • z.val
      --   → negSph z ∈ s (i.e. ⟨-z.val,...⟩ ∈ s)
      --   → -(r • z.val) = r • (negSph z).val ∈ Ioo • val'' s
      rintro ⟨r, hr, v, ⟨z, hz, rfl⟩, rfl⟩
      -- hz : z ∈ negSph ⁻¹' s, i.e., negSph z ∈ s
      -- goal: -(r • z.val) ∈ Ioo • val'' s
      refine ⟨r, hr, (negSph z).val, ⟨negSph z, hz, rfl⟩, ?_⟩
      simp [negSph, smul_neg]
    · -- Backward: -y = r • x.val for x ∈ s, so y = r • (-x.val)
      --   → ⟨-x.val,...⟩ ∈ negSph ⁻¹' s (since negSph maps it to x ∈ s)
      rintro ⟨r, hr, v, ⟨x, hxs, rfl⟩, h⟩
      -- h : r • x.val = -y, so y = -(r • x.val) = r • (-x.val)
      -- Let w = ⟨-x.val, ...⟩
      let w : Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
        ⟨-x.val, mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact norm_eq_of_mem_sphere x)⟩
      refine ⟨r, hr, w.val, ⟨w, ?_, rfl⟩, ?_⟩
      · -- w ∈ negSph ⁻¹' s: negSph w = ⟨-(-x.val),...⟩ which equals x ∈ s
        simp only [Set.mem_preimage]
        convert hxs using 1
        ext; simp [negSph, w]
      · -- r • w.val = y: w.val = -x.val, r • (-x.val) = -(r • x.val) = -(-y) = y
        have h' : r • x.val = -y := h
        -- w.val = -x.val, so r • w.val = r • (-x.val) = -(r • x.val) = -(-y) = y
        change r • w.val = y
        simp only [w, smul_neg, h', neg_neg]
  intro T₁ T₂ h
  rw [h, ← hmembed.map_apply (V_perp_haar Φ), hinv]

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

-- Helper: the raw sphere measure is invariant under linear isometries of V_perp.
private lemma V_perp_rawSph_isometry_invariant (Φ : E n)
    (f : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ)) :
    let fSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
      fun x => ⟨f x.val,
        mem_sphere_zero_iff_norm.mpr (by rw [f.norm_map]; exact norm_eq_of_mem_sphere x)⟩
    Measure.map fSph (V_perp_rawSph Φ) = V_perp_rawSph Φ := by
  intro fSph
  have hb : BorelSpace ↥(V_perp Φ) := inferInstance
  have hfSph_meas : Measurable fSph := by
    have hcont : Continuous fSph := (f.continuous.comp continuous_subtype_val).subtype_mk _
    letI : BorelSpace (Metric.sphere (0 : ↥(V_perp Φ)) 1) := inferInstance
    exact hcont.measurable
  have hf_meas : Measurable (f : ↥(V_perp Φ) → ↥(V_perp Φ)) :=
    @Continuous.measurable _ _ _ _ (@BorelSpace.opensMeasurable _ _ _ hb) _ _ hb
      (f : ↥(V_perp Φ) → ↥(V_perp Φ)) f.continuous
  have hf_symm_meas : Measurable (f.symm : ↥(V_perp Φ) → ↥(V_perp Φ)) :=
    @Continuous.measurable _ _ _ _ (@BorelSpace.opensMeasurable _ _ _ hb) _ _ hb
      (f.symm : ↥(V_perp Φ) → ↥(V_perp Φ)) f.symm.continuous
  have hmembed : MeasurableEmbedding (f : ↥(V_perp Φ) → ↥(V_perp Φ)) :=
    ⟨f.injective, hf_meas, fun {s} hs => by
      rw [Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply]
      exact hf_symm_meas hs⟩
  have hinv := V_perp_haar_map_isometry Φ f
  suffices h : ∀ (t : Set (Metric.sphere (0 : ↥(V_perp Φ)) 1)),
      MeasurableSet t →
      @Measure.toSphere _ _ _ _ (V_perp_haar Φ) (fSph ⁻¹' t) =
      @Measure.toSphere _ _ _ _ (V_perp_haar Φ) t by
    ext s hs
    simp only [V_perp_rawSph, Measure.map_apply hfSph_meas hs]
    exact h s hs
  intro s hs
  rw [@Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ) hb _ (hs.preimage hfSph_meas),
      @Measure.toSphere_apply' _ _ _ _ (V_perp_haar Φ) hb _ hs]
  congr 1
  suffices hsets : ∀ (T₁ T₂ : Set ↥(V_perp Φ)),
      T₁ = f ⁻¹' T₂ → (V_perp_haar Φ) T₁ = (V_perp_haar Φ) T₂ by
    apply hsets
    ext y
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, v, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, (fSph z).val, ⟨fSph z, hz, rfl⟩, by simp [fSph, map_smul]⟩
    · rintro ⟨r, hr, v, ⟨x, hxs, rfl⟩, h⟩
      let w : Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
        ⟨f.symm x.val, mem_sphere_zero_iff_norm.mpr
          (by rw [f.symm.norm_map]; exact norm_eq_of_mem_sphere x)⟩
      refine ⟨r, hr, w.val, ⟨w, ?_, rfl⟩, ?_⟩
      · simp only [Set.mem_preimage]
        convert hxs using 1
        ext; simp [fSph, w, f.apply_symm_apply]
      · have hy : r • f.symm x.val = y := by
          have h1 := f.symm_apply_apply y
          rw [← h, map_smul] at h1
          exact h1
        exact hy
  intro T₁ T₂ hT
  rw [hT, ← hmembed.map_apply (V_perp_haar Φ), hinv]

/-- The perpSphereMeasure is invariant under negation (antipodal symmetry). -/
lemma perpSphereMeasure_neg_invariant (Φ : E n) :
    Measure.map Neg.neg (perpSphereMeasure Φ) = perpSphereMeasure Φ := by
  simp only [perpSphereMeasure]
  set rawSph := V_perp_rawSph Φ
  set totalMass := rawSph Set.univ
  set toEn := fun (x : Metric.sphere (0 : ↥(V_perp Φ)) 1) =>
      ((x.val : ↥(V_perp Φ)) : E n)
  have htoEn_meas : Measurable toEn :=
    measurable_subtype_coe.comp measurable_subtype_coe
  -- Define negSph explicitly (avoiding InvolutiveNeg instance synthesis issue)
  let negSph : Metric.sphere (0 : ↥(V_perp Φ)) 1 → Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
    fun x => ⟨-x.val,
      mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact norm_eq_of_mem_sphere x)⟩
  have hnegSph_meas : Measurable negSph :=
    ((continuous_neg.comp continuous_subtype_val).subtype_mk _).measurable
  -- Key commutativity: Neg.neg ∘ toEn = toEn ∘ negSph
  -- i.e., -(↑↑x : E n) = ↑↑(negSph x) for x : sphere (↥(V_perp Φ)) 1
  have hcomm : (Neg.neg : E n → E n) ∘ toEn = toEn ∘ negSph := by
    ext x
    simp only [Function.comp, toEn, negSph, Submodule.coe_neg]
  rw [Measure.map_map measurable_neg htoEn_meas, hcomm,
      ← Measure.map_map htoEn_meas hnegSph_meas,
      Measure.map_smul, V_perp_rawSph_neg_invariant]

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
  have hd : 2 ≤ d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
  haveI : IsProbabilityMeasure (composedMeasure (d n) G σ) :=
    composedMeasure_isProbMeasure (d n) G σ hσ hG hd
  simp_rw [integral_e₂_succProb Φ _ w]
  -- Goal: ∫ θ, (cos²θ · p + sin²θ · q) ∂μ = f₂·p + (1-f₂)·q
  -- where f₂ = ∫ cos²θ ∂μ definitionally
  set μ := composedMeasure (d n) G σ
  have hcos_int : Integrable (fun θ => cos θ ^ 2) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (continuous_cos.pow 2).measurable.aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsin_int : Integrable (fun θ => sin θ ^ 2) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (continuous_sin.pow 2).measurable.aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have hf₂_def : f₂ (d n) G σ = ∫ θ, cos θ ^ 2 ∂μ := rfl
  have hsin_f₂ : ∫ θ, sin θ ^ 2 ∂μ = 1 - f₂ (d n) G σ := by
    have hsum : ∫ θ, (cos θ ^ 2 + sin θ ^ 2) ∂μ = 1 := by
      simp_rw [Real.cos_sq_add_sin_sq]
      simp
    rw [integral_add hcos_int hsin_int] at hsum
    linarith [hf₂_def]
  -- Rewrite integrand and do the integration
  have hfun : (fun θ => cos θ ^ 2 * succProb n Φ w +
      sin θ ^ 2 * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ)) =
      fun θ => succProb n Φ w * cos θ ^ 2 +
               (∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ)) * sin θ ^ 2 := by
    ext θ; ring
  rw [hfun]
  rw [integral_add (hcos_int.const_mul _) (hsin_int.const_mul _)]
  rw [show (∫ a, succProb n Φ w * cos a ^ 2 ∂μ) = succProb n Φ w * ∫ a, cos a ^ 2 ∂μ from
        integral_const_mul _ _,
      show (∫ a, (∫ e₂, succProb n e₂ w ∂perpSphereMeasure Φ) * sin a ^ 2 ∂μ) =
        (∫ e₂, succProb n e₂ w ∂perpSphereMeasure Φ) * ∫ a, sin a ^ 2 ∂μ from
        integral_const_mul _ _]
  rw [hsin_f₂, ← hf₂_def]
  ring

/-! ## Isometry invariance helpers for the Schur argument -/

-- Helper: any submodule of V_perp has HasOrthogonalProjection
-- (via FiniteDimensional → closed → complete → HasOrthogonalProjection)
private lemma V_perp_submodule_hasOrthogonalProjection (Φ : E n)
    (K : Submodule ℝ ↥(V_perp Φ)) : K.HasOrthogonalProjection := by
  haveI : IsUniformAddGroup ↥(V_perp Φ) :=
    (V_perp Φ).toAddSubgroup.isUniformAddGroup
  constructor
  intro v
  have hc : IsComplete (K : Set ↥(V_perp Φ)) :=
    K.complete_of_finiteDimensional
  obtain ⟨w, hwK, hw⟩ :=
    K.exists_norm_eq_iInf_of_complete_subspace hc v
  exact ⟨w, hwK, (K.mem_orthogonal' _).2
    ((K.norm_eq_iInf_iff_inner_eq_zero hwK).mp hw)⟩

/-- Off-diagonal vanishing: for orthogonal u, v ∈ V_perp, ∫ ⟨e₂,u⟩⟨e₂,v⟩ dμ = 0.
    Uses reflection in (span{u})ᗮ inside V_perp: the reflection negates the u-component
    and preserves the v-component, while the sphere measure is invariant. -/
lemma integral_perpSphere_inner_mul_ortho (Φ : E n)
    (u v : ↥(V_perp Φ)) (huv : ⟪(u : E n), (v : E n)⟫_ℝ = 0) :
    ∫ e₂, ⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ ∂(perpSphereMeasure Φ) = 0 := by
  -- Unfold perpSphereMeasure
  simp only [perpSphereMeasure]
  set rawSph := V_perp_rawSph Φ with rawSph_def
  set totalMass := rawSph Set.univ
  set toEn : Metric.sphere (0 : ↥(V_perp Φ)) 1 → E n :=
    fun x => ((x.val : ↥(V_perp Φ)) : E n)
  have htoEn_meas : Measurable toEn :=
    measurable_subtype_coe.comp measurable_subtype_coe
  -- Rewrite as sphere integral using integral_map
  have hf_cont : Continuous (fun e₂ : E n =>
      ⟪e₂, (u : E n)⟫_ℝ * ⟪e₂, (v : E n)⟫_ℝ) :=
    (continuous_id.inner continuous_const (𝕜 := ℝ)).mul
     (continuous_id.inner continuous_const (𝕜 := ℝ))
  rw [integral_map htoEn_meas.aemeasurable
    hf_cont.aestronglyMeasurable]
  -- Construct the reflection R in (span{u})ᗮ inside V_perp
  let K : Submodule ℝ ↥(V_perp Φ) :=
    (Submodule.span ℝ {(u : ↥(V_perp Φ))})ᗮ
  haveI : K.HasOrthogonalProjection :=
    V_perp_submodule_hasOrthogonalProjection Φ K
  let R : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ) := K.reflection
  -- Define fSph (R restricted to sphere)
  let fSph :
      Metric.sphere (0 : ↥(V_perp Φ)) 1 →
        Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
    fun x => ⟨R x.val,
      mem_sphere_zero_iff_norm.mpr
        (by rw [R.norm_map]; exact norm_eq_of_mem_sphere x)⟩
  have hfSph_cont : Continuous fSph :=
    (R.continuous.comp continuous_subtype_val).subtype_mk _
  letI : BorelSpace (Metric.sphere (0 : ↥(V_perp Φ)) 1) :=
    inferInstance
  have hfSph_meas : Measurable fSph := hfSph_cont.measurable
  -- Measure invariance
  have hinv : Measure.map fSph rawSph = rawSph :=
    V_perp_rawSph_isometry_invariant Φ R
  have hinv_norm :
      Measure.map fSph (totalMass⁻¹ • rawSph) =
        totalMass⁻¹ • rawSph := by
    rw [Measure.map_smul, hinv]
  -- Set up the integrand
  set h :=
    fun (x : Metric.sphere (0 : ↥(V_perp Φ)) 1) =>
      ⟪(toEn x), (u : E n)⟫_ℝ * ⟪(toEn x), (v : E n)⟫_ℝ
  -- Self-adjointness of R: ⟪R a, b⟫ = ⟪a, R b⟫
  have hR_adj :
      ∀ a b : ↥(V_perp Φ), ⟪R a, b⟫_ℝ = ⟪a, R b⟫_ℝ := by
    intro a b
    have h1 := R.inner_map_map a (R b)
    simp only [R, Submodule.reflection_reflection] at h1
    exact h1
  -- R u = -u (reflection in K = (span{u})ᗮ negates u)
  have hRu : R (u : ↥(V_perp Φ)) = -u := by
    change K.reflection u = -u
    exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _
  -- v ∈ (span{u})ᗮ inside V_perp
  have hv_mem : (v : ↥(V_perp Φ)) ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [Submodule.coe_inner]
    rw [real_inner_comm]; exact huv
  -- R v = v
  have hRv : R (v : ↥(V_perp Φ)) = v :=
    Submodule.reflection_mem_subspace_eq_self hv_mem
  -- The integrand transforms: h(fSph x) = -h(x)
  have htransform :
      ∀ x : Metric.sphere (0 : ↥(V_perp Φ)) 1,
        h (fSph x) = -h x := by
    intro x
    simp only [h, fSph, toEn]
    have h1 :
        ⟪((R x.val : ↥(V_perp Φ)) : E n), (u : E n)⟫_ℝ =
          -⟪((x.val : ↥(V_perp Φ)) : E n), (u : E n)⟫_ℝ := by
      rw [← Submodule.coe_inner, ← Submodule.coe_inner,
        hR_adj, hRu]
      simp [Submodule.coe_inner]
    have h2 :
        ⟪((R x.val : ↥(V_perp Φ)) : E n), (v : E n)⟫_ℝ =
          ⟪((x.val : ↥(V_perp Φ)) : E n), (v : E n)⟫_ℝ := by
      rw [← Submodule.coe_inner, ← Submodule.coe_inner,
        hR_adj, hRv]
    rw [h1, h2, neg_mul]
  -- Use invariance to rewrite
  have heq :
      ∫ x, h x ∂(totalMass⁻¹ • rawSph) =
        ∫ x, h (fSph x) ∂(totalMass⁻¹ • rawSph) := by
    conv_lhs => rw [← hinv_norm]
    have hasm2 :
        AEStronglyMeasurable
          (fun x : Metric.sphere (0 : ↥(V_perp Φ)) 1 =>
            ⟪(toEn x), (u : E n)⟫_ℝ *
              ⟪(toEn x), (v : E n)⟫_ℝ)
          (Measure.map fSph (totalMass⁻¹ • rawSph)) :=
      (hf_cont.comp
        (continuous_subtype_val.comp
          continuous_subtype_val)).aestronglyMeasurable
    rw [integral_map hfSph_meas.aemeasurable hasm2]
  -- So ∫ h = ∫ (-h) = -∫ h, hence ∫ h = 0
  have heq2 :
      ∫ x, h x ∂(totalMass⁻¹ • rawSph) =
        -(∫ x, h x ∂(totalMass⁻¹ • rawSph)) := by
    conv_lhs => rw [heq]
    simp only [htransform]
    exact integral_neg (fun x => h x)
  linarith

/-- Diagonal equality: for unit u, v ∈ V_perp, ∫ ⟨e₂,u⟩² = ∫ ⟨e₂,v⟩².
    Uses Householder reflection (span{u-v})ᗮ inside V_perp which maps
    u ↦ v (by reflection_sub), while the sphere measure is invariant. -/
lemma integral_perpSphere_inner_sq_eq (Φ : E n)
    (u v : ↥(V_perp Φ)) (hu : ‖(u : E n)‖ = 1)
    (hv : ‖(v : E n)‖ = 1) :
    ∫ e₂, ⟪e₂, (u : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
    ∫ e₂, ⟪e₂, (v : E n)⟫_ℝ ^ 2
      ∂(perpSphereMeasure Φ) := by
  -- Handle the trivial case u = v
  by_cases huv : u = v
  · rw [huv]
  -- For u ≠ v, construct Householder reflection
  -- Unfold perpSphereMeasure
  simp only [perpSphereMeasure]
  set rawSph := V_perp_rawSph Φ with rawSph_def
  set totalMass := rawSph Set.univ
  set toEn : Metric.sphere (0 : ↥(V_perp Φ)) 1 → E n :=
    fun x => ((x.val : ↥(V_perp Φ)) : E n)
  have htoEn_meas : Measurable toEn :=
    measurable_subtype_coe.comp measurable_subtype_coe
  -- Rewrite as sphere integral using integral_map
  have hg_cont : Continuous (fun e₂ : E n =>
      ⟪e₂, (u : E n)⟫_ℝ ^ 2) :=
    (continuous_id.inner continuous_const (𝕜 := ℝ)).pow 2
  have hasm_u :
      AEStronglyMeasurable
        (fun e₂ : E n => ⟪e₂, (u : E n)⟫_ℝ ^ 2)
        (Measure.map toEn (totalMass⁻¹ • rawSph)) :=
    hg_cont.aestronglyMeasurable
  have hg_cont_v : Continuous (fun e₂ : E n =>
      ⟪e₂, (v : E n)⟫_ℝ ^ 2) :=
    (continuous_id.inner continuous_const (𝕜 := ℝ)).pow 2
  have hasm_v :
      AEStronglyMeasurable
        (fun e₂ : E n => ⟪e₂, (v : E n)⟫_ℝ ^ 2)
        (Measure.map toEn (totalMass⁻¹ • rawSph)) :=
    hg_cont_v.aestronglyMeasurable
  rw [integral_map htoEn_meas.aemeasurable hasm_u,
    integral_map htoEn_meas.aemeasurable hasm_v]
  -- Construct Householder reflection in V_perp
  let K : Submodule ℝ ↥(V_perp Φ) :=
    (Submodule.span ℝ
      {(u : ↥(V_perp Φ)) - (v : ↥(V_perp Φ))})ᗮ
  haveI : K.HasOrthogonalProjection :=
    V_perp_submodule_hasOrthogonalProjection Φ K
  let R : ↥(V_perp Φ) ≃ₗᵢ[ℝ] ↥(V_perp Φ) := K.reflection
  -- R u = v by reflection_sub
  have hRu :
      R (u : ↥(V_perp Φ)) = (v : ↥(V_perp Φ)) := by
    change K.reflection u = v
    exact Submodule.reflection_sub (by
      have hu' : ‖u‖ = 1 := hu
      have hv' : ‖v‖ = 1 := hv
      rw [hu', hv'])
  -- Self-adjointness of R
  have hR_adj :
      ∀ a b : ↥(V_perp Φ), ⟪R a, b⟫_ℝ = ⟪a, R b⟫_ℝ := by
    intro a b
    have h1 := R.inner_map_map a (R b)
    simp only [R, Submodule.reflection_reflection] at h1
    exact h1
  -- Define fSph (R restricted to sphere)
  let fSph :
      Metric.sphere (0 : ↥(V_perp Φ)) 1 →
        Metric.sphere (0 : ↥(V_perp Φ)) 1 :=
    fun x => ⟨R x.val,
      mem_sphere_zero_iff_norm.mpr
        (by rw [R.norm_map]; exact norm_eq_of_mem_sphere x)⟩
  have hfSph_cont : Continuous fSph :=
    (R.continuous.comp continuous_subtype_val).subtype_mk _
  letI : BorelSpace (Metric.sphere (0 : ↥(V_perp Φ)) 1) :=
    inferInstance
  have hfSph_meas : Measurable fSph := hfSph_cont.measurable
  -- Measure invariance
  have hinv : Measure.map fSph rawSph = rawSph :=
    V_perp_rawSph_isometry_invariant Φ R
  have hinv_norm :
      Measure.map fSph (totalMass⁻¹ • rawSph) =
        totalMass⁻¹ • rawSph := by
    rw [Measure.map_smul, hinv]
  -- The integrand transforms: ⟪toEn(fSph x), u⟫² = ⟪toEn x, v⟫²
  have htransform :
      ∀ x : Metric.sphere (0 : ↥(V_perp Φ)) 1,
        ⟪toEn (fSph x), (u : E n)⟫_ℝ ^ 2 =
          ⟪toEn x, (v : E n)⟫_ℝ ^ 2 := by
    intro x
    simp only [fSph, toEn]
    have :
        ⟪((R x.val : ↥(V_perp Φ)) : E n),
            (u : E n)⟫_ℝ =
          ⟪((x.val : ↥(V_perp Φ)) : E n),
            (v : E n)⟫_ℝ := by
      rw [← Submodule.coe_inner, ← Submodule.coe_inner,
        hR_adj, hRu]
    rw [this]
  -- Use invariance: ∫ ⟨e₂,u⟩² = ∫ ⟨e₂,u⟩² ∘ fSph = ∫ ⟨e₂,v⟩²
  conv_lhs => rw [← hinv_norm]
  have hasm3 :
      AEStronglyMeasurable
        (fun x : Metric.sphere (0 : ↥(V_perp Φ)) 1 =>
          ⟪(toEn x), (u : E n)⟫_ℝ ^ 2)
        (Measure.map fSph (totalMass⁻¹ • rawSph)) :=
    (hg_cont.comp
      (continuous_subtype_val.comp
        continuous_subtype_val)).aestronglyMeasurable
  rw [integral_map hfSph_meas.aemeasurable hasm3]
  congr 1; ext x; exact htransform x

/-! ## TDD spot-checks -/

-- V_perp contains vectors orthogonal to Φ
example (i j : Fin (d n)) (hij : i ≠ j) :
    stdBasisVec n j ∈ V_perp (stdBasisVec n i) := by
  rw [mem_V_perp_iff]
  have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
              (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d n)))
  have key : inner (𝕜 := ℝ) (stdBasisVec n i) (stdBasisVec n j) = if i = j then 1 else 0 := by
    simp only [stdBasisVec]
    exact h i j
  rw [key, if_neg hij]

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

end IsotropicGrover
