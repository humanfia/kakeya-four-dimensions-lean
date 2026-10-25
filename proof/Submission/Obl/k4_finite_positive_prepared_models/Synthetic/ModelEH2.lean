import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Model
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Caps

/-!
# The caps `EH2` of the synthetic stage model

The palette is uniform on `[0, β]`, so its bins of width `N^(-v)` carry at most
`2^B N^(-v) ≤ K N^(-S v)`. Both hidden observables of the model are the hidden coordinate
itself (`P = X₃`), and the cell caps give the pure and joint ceilings with the constant
`2^(e+1) ≤ K`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set MvPolynomial

noncomputable section

namespace Par

variable (p : Par)

theorem pal_bin_le (v : ℝ) (hv : 0 ≤ v) (S : ℝ) (hS : S ≤ 1) (a : ℤ) :
    p.synth.pal {w : ℝ | ⌊w / p.sN ^ (-v)⌋ = a} ≤ ENNReal.ofReal (p.sK * p.sN ^ (-S * v)) := by
  set ε := p.sN ^ (-v) with hε
  have hεpos : 0 < ε := by rw [hε, sN_rpow]; positivity
  have hβ := p.synth.β_pos
  have hset : {w : ℝ | ⌊w / ε⌋ = a} = Ico ((a : ℝ) * ε) ((a : ℝ) * ε + ε) := by
    ext w; exact floor_div_eq_iff hεpos a
  rw [hset, p.synth.pal_apply measurableSet_Ico]
  have hpre : {u : ℝ | p.synth.β * u ∈ Ico ((a : ℝ) * ε) ((a : ℝ) * ε + ε)} =
      Ico ((a : ℝ) * ε / p.synth.β) (((a : ℝ) * ε + ε) / p.synth.β) := by
    ext u
    simp only [mem_ofPred_eq, mem_Ico]
    rw [div_le_iff₀ hβ, lt_div_iff₀ hβ, mul_comm u]
  rw [hpre]
  refine (U_le_volume _).trans ?_
  rw [Real.volume_Ico]
  apply ENNReal.ofReal_le_ofReal
  have e1 : ((a : ℝ) * ε + ε) / p.synth.β - (a : ℝ) * ε / p.synth.β = ε * 2 ^ p.synth.B := by
    have : p.synth.β = 1 / 2 ^ p.synth.B := rfl
    rw [this]; field_simp; ring
  rw [e1, hε, sN_rpow, sN_rpow, sK_eq]
  rw [show (2 : ℝ) ^ p.synth.B = (2 : ℝ) ^ (p.synth.B : ℝ) by norm_cast,
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  apply two_rpow_le
  have hBσ : (p.synth.B : ℝ) ≤ p.σ := by
    have := p.σ_ge
    have : (0 : ℝ) ≤ p.n := by positivity
    show (p.B : ℝ) ≤ p.σ
    linarith
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have : (p.Λ : ℝ) * (S * v) ≤ p.Λ * v := by
    apply mul_le_mul_of_nonneg_left _ hΛ
    nlinarith
  nlinarith

theorem measurable_sbS_apply (k : Fin 6) :
    Measurable (fun x : (ℕ × (Fin 6 → ℝ)) × ℝ => p.synth.sbS x.1 k) :=
  (measurable_pi_apply k).comp (p.synth.measurable_sbS.comp measurable_fst)

theorem measurable_zS (r : ℝ) : Measurable (fun x : (ℕ × (Fin 6 → ℝ)) × ℝ =>
    zS p.synth.sbS p.sN r x) := by
  refine measurable_pi_iff.mpr fun k => ?_
  have h0 := p.measurable_sbS_apply 0
  have h1 := p.measurable_sbS_apply 1
  have h3 := p.measurable_sbS_apply 3
  have h4 := p.measurable_sbS_apply 4
  unfold zS exS
  fin_cases k
  · exact Int.measurable_floor.comp (measurable_snd.div_const _)
  · exact Int.measurable_floor.comp ((h0.add (measurable_snd.mul h3)).div_const _)
  · exact Int.measurable_floor.comp ((h1.add (measurable_snd.mul h4)).div_const _)

theorem hidden_obs (h : Bool) (x : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    (if h then eval (exS p.synth.sbS x.1 x.2) (X 3) else (exS p.synth.sbS x.1 x.2) 3) =
      hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2) := by
  cases h
  · simp [exS, Synth.sbS]
  · simp only [ite_true]; exact p.eval_exS_X3 _ _

/-- The hidden generation used for a hidden bin. -/
def gen (s : ℝ) : ℕ := ⌊s * p.Λ / p.e⌋₊

theorem gen_le (s : ℝ) (hs : s ≤ p.n) : p.gen s ≤ p.synth.G := by
  unfold gen
  show ⌊s * p.Λ / p.e⌋₊ ≤ p.G
  apply Nat.floor_le_of_le
  unfold G e
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have := p.n_pos
  have k1 : s * p.Λ ≤ p.n * p.Λ := by nlinarith
  have k2 : (p.n : ℝ) * p.Λ ≤ p.n * p.Λ * (p.n + 1) := by
    have : (0 : ℝ) ≤ p.n * p.Λ := by positivity
    nlinarith
  linarith

theorem gen_bin (s : ℝ) (hs : 0 ≤ s) : p.sN ^ (-s) ≤ 1 / 2 ^ (p.synth.e * p.gen s) := by
  rw [sN_rpow, one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  apply two_rpow_le
  have he : (0 : ℝ) < p.e := by unfold e; positivity
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have h1 : ((p.gen s : ℕ) : ℝ) ≤ s * p.Λ / p.e :=
    Nat.floor_le (div_nonneg (mul_nonneg hs hΛ) he.le)
  have : ((p.synth.e * p.gen s : ℕ) : ℝ) ≤ s * p.Λ := by
    push_cast
    show (p.e : ℝ) * p.gen s ≤ s * p.Λ
    rw [le_div_iff₀ he] at h1
    linarith
  linarith

theorem gen_mass (s : ℝ) (hs : 0 ≤ s) :
    2 * ((2 : ENNReal) ^ (p.synth.e₁ * p.gen s))⁻¹ ≤
      ENNReal.ofReal (2 ^ ((p.e : ℝ) + 1) * p.sN ^ (-(p.d₁ * s))) := by
  have he : (0 : ℝ) < p.e := by unfold e; positivity
  have hd₁ := p.hd₁
  -- e₁ ≥ d₁ e and e·gen > sΛ - e
  have he₁ : p.d₁ * p.e ≤ p.e₁ := Nat.le_ceil _
  have hg : s * p.Λ / p.e < (p.gen s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hg' : s * p.Λ - p.e < p.e * p.gen s := by
    rw [div_lt_iff₀ he] at hg; linarith
  have hkey : p.d₁ * (s * p.Λ) - p.e ≤ p.e₁ * p.gen s := by
    have h0 : (0 : ℝ) ≤ p.gen s := by positivity
    have : p.d₁ * (p.e * p.gen s) ≤ p.e₁ * p.gen s := by nlinarith
    have hd₁1 : p.d₁ ≤ 1 := p.hd₁'.le
    have : p.d₁ * (s * p.Λ - p.e) ≤ p.d₁ * (p.e * p.gen s) := by nlinarith
    nlinarith
  have e2 : (2 : ENNReal) * ((2 : ENNReal) ^ (p.synth.e₁ * p.gen s))⁻¹ =
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-((p.e₁ * p.gen s : ℕ) : ℝ))) := by
    rw [ENNReal.ofReal_mul (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_natCast,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
    rfl
  rw [e2]
  apply ENNReal.ofReal_le_ofReal
  rw [sN_rpow, ← Real.rpow_add (by norm_num)]
  calc 2 * (2 : ℝ) ^ (-((p.e₁ * p.gen s : ℕ) : ℝ)) = (2 : ℝ) ^ (1 - ((p.e₁ * p.gen s : ℕ) : ℝ)) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]; ring
    _ ≤ (2 : ℝ) ^ ((p.e : ℝ) + 1 + p.Λ * -(p.d₁ * s)) := by
        apply two_rpow_le
        push_cast
        nlinarith

/-- The cell set of the model, with the hidden observable made explicit. -/
def cellSet (r s : ℝ) (q : Fin 3 → ℤ) (a : ℤ) (V : Set ℝ) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {x | zS p.synth.sbS p.sN r x = q ∧
    ⌊hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2) / p.sN ^ (-s)⌋ = a ∧
    p.synth.sbS x.1 3 ∈ V}

theorem cellSet_eq (r s : ℝ) (q : Fin 3 → ℤ) (a : ℤ) (V : Set ℝ) (h : Bool) :
    {x | zS p.synth.sbS p.sN r x = q ∧
      ⌊(if h then eval (exS p.synth.sbS x.1 x.2) (X 3) else (exS p.synth.sbS x.1 x.2) 3) /
        p.sN ^ (-s)⌋ = a ∧ p.synth.sbS x.1 3 ∈ V} = p.cellSet r s q a V := by
  ext x
  simp only [cellSet, mem_ofPred_eq, p.hidden_obs h x]

theorem measurableSet_cellSet (r s : ℝ) (q : Fin 3 → ℤ) (a : ℤ) {V : Set ℝ}
    (hV : MeasurableSet V) : MeasurableSet (p.cellSet r s q a V) := by
  have hh : Measurable (fun x : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2)) :=
    p.synth.measurable_hidl.comp measurable_fst
  have h1 : MeasurableSet {x : (ℕ × (Fin 6 → ℝ)) × ℝ | zS p.synth.sbS p.sN r x = q} := by
    have e : {x : (ℕ × (Fin 6 → ℝ)) × ℝ | zS p.synth.sbS p.sN r x = q} =
        ⋂ k : Fin 3, (fun x => zS p.synth.sbS p.sN r x k) ⁻¹' {q k} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff]
      exact ⟨fun h k => congrFun h k, fun h => funext h⟩
    rw [e]
    exact MeasurableSet.iInter fun k =>
      (measurable_pi_iff.mp (p.measurable_zS r) k) (MeasurableSet.of_discrete)
  have h2 : MeasurableSet {x : (ℕ × (Fin 6 → ℝ)) × ℝ |
      ⌊hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2) / p.sN ^ (-s)⌋ = a} :=
    measurableSet_eq_fun (Int.measurable_floor.comp (hh.div_const _)) measurable_const
  have h3 : MeasurableSet {x : (ℕ × (Fin 6 → ℝ)) × ℝ | p.synth.sbS x.1 3 ∈ V} :=
    (p.measurable_sbS_apply 3) hV
  exact h1.inter (h2.inter h3)

/-- The sample set of a cell. -/
def cellΩ (r s : ℝ) (q : Fin 3 → ℤ) (a : ℤ) (V : Set ℝ) : Set (Ω × ℝ) :=
  {x | ⌊x.2 / p.sN ^ (-r)⌋ = q 0 ∧
    ⌊(x.1.2.1.1 + x.2 * (p.synth.β * x.1.2.1.2)) / p.sN ^ (-r)⌋ = q 1 ∧
    ⌊x.1.2.2 / p.sN ^ (-r)⌋ = q 2 ∧
    ⌊hid p.synth.e p.synth.e₁ p.synth.G x.1.1.1 x.1.1.2 / p.sN ^ (-s)⌋ = a ∧
    p.synth.β * x.1.2.1.2 ∈ V}

theorem preimage_cellSet (r s : ℝ) (q : Fin 3 → ℤ) (a : ℤ) (V : Set ℝ) :
    Prod.map emb id ⁻¹' p.cellSet r s q a V ⊆ p.cellΩ r s q a V := by
  rintro ⟨ω, t⟩ ⟨hz, hhid, hv⟩
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  simp only [zS, exS, Prod.map, id, Synth.sbS, emb] at h0 h1 h2 hhid hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val, mul_zero, add_zero] at h0 h1 h2 hhid hv
  exact ⟨h0, h1, h2, hhid, hv⟩

theorem cap_numeric (r s : ℝ) :
    p.sN ^ (-r) * (2 ^ ((p.e : ℝ) + 1) * p.sN ^ (-(p.d₁ * s))) * p.sN ^ (-r) * p.sN ^ (-r) ≤
      p.sK * p.sN ^ (-3 * r - p.d₁ * s) := by
  rw [sN_rpow, sN_rpow, sN_rpow, sK_eq]
  rw [show (2 : ℝ) ^ ((p.Λ : ℝ) * -r) * ((2 : ℝ) ^ ((p.e : ℝ) + 1) *
      (2 : ℝ) ^ ((p.Λ : ℝ) * -(p.d₁ * s))) * (2 : ℝ) ^ ((p.Λ : ℝ) * -r) *
      (2 : ℝ) ^ ((p.Λ : ℝ) * -r) =
      (2 : ℝ) ^ ((p.e : ℝ) + 1 + p.Λ * (-3 * r - p.d₁ * s)) by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring]
  rw [← Real.rpow_add (by norm_num)]
  apply two_rpow_le
  have : (p.e : ℝ) + 1 ≤ p.σ := by
    have := p.σ_ge
    have : (0 : ℝ) ≤ p.B := by positivity
    unfold e; push_cast; linarith
  linarith

/-- **Model cell cap.** -/
theorem cap_model (r s : ℝ) (hs0 : 0 ≤ s) (hsn : s ≤ p.n) (q : Fin 3 → ℤ) (a : ℤ)
    {V : Set ℝ} (hV : MeasurableSet V) :
    p.synth.mu (p.cellSet r s q a V) ≤
      ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) * U {u | p.synth.β * u ∈ V} := by
  have hεpos : 0 < p.sN ^ (-r) := by rw [sN_rpow]; positivity
  have hε'pos : 0 < p.sN ^ (-s) := by rw [sN_rpow]; positivity
  have hm := p.measurableSet_cellSet r s q a hV
  calc p.synth.mu (p.cellSet r s q a V) ≤ (p.synth.nu.prod volume) (p.cellSet r s q a V) :=
        p.synth.mu_le _
    _ = ((P p.synth.M).prod (volume : Measure ℝ)) (Prod.map emb id ⁻¹' p.cellSet r s q a V) := by
        rw [← p.synth.prod_map_emb, Measure.map_apply Synth.measurable_embid hm]
    _ ≤ ((P p.synth.M).prod (volume : Measure ℝ)) (p.cellΩ r s q a V) :=
        measure_mono (p.preimage_cellSet r s q a V)
    _ ≤ ENNReal.ofReal (p.sN ^ (-r)) * ((2 * ((2 : ENNReal) ^ (p.synth.e₁ * p.gen s))⁻¹) *
        ((ENNReal.ofReal (p.sN ^ (-r)) * U {u | p.synth.β * u ∈ V}) *
          ENNReal.ofReal (p.sN ^ (-r)))) :=
        p.synth.cap_core hεpos hε'pos _ _ _ _ hV (p.gen_le s hsn) (p.gen_bin s hs0)
    _ ≤ ENNReal.ofReal (p.sN ^ (-r)) *
        (ENNReal.ofReal (2 ^ ((p.e : ℝ) + 1) * p.sN ^ (-(p.d₁ * s))) *
        ((ENNReal.ofReal (p.sN ^ (-r)) * U {u | p.synth.β * u ∈ V}) *
          ENNReal.ofReal (p.sN ^ (-r)))) := by
        gcongr; exact p.gen_mass s hs0
    _ = ENNReal.ofReal (p.sN ^ (-r) * (2 ^ ((p.e : ℝ) + 1) * p.sN ^ (-(p.d₁ * s))) *
        p.sN ^ (-r) * p.sN ^ (-r)) * U {u | p.synth.β * u ∈ V} := by
        have a1 : 0 ≤ p.sN ^ (-r) := hεpos.le
        have a2 : 0 ≤ 2 ^ ((p.e : ℝ) + 1) * p.sN ^ (-(p.d₁ * s)) := by
          rw [sN_rpow]; positivity
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg a1 a2) a1),
          ENNReal.ofReal_mul (mul_nonneg a1 a2), ENNReal.ofReal_mul a1]
        ring
    _ ≤ ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) * U {u | p.synth.β * u ∈ V} :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (p.cap_numeric r s)) _

/-- **`EH2`.** -/
theorem eh2 (S : ℝ) (hS : S ≤ 1) (R : ℝ) (hR : 1 < R) (hRn : R ≤ p.n) :
    EH2 p.d₁ S p.stage R := by
  intro r s v hr1 hr2 hs1 hs2 hv1 hv2
  have hR0 : 0 < R := by linarith
  have hv0 : 0 ≤ v := le_trans (inv_nonneg.mpr hR0.le) hv1
  have hsn : s ≤ p.n := hs2.trans hRn
  refine ⟨fun a => p.pal_bin_le v hv0 S hS a, fun h q a => ?_, fun h q a v₀ => ?_⟩
  · have hsub : {x : (ℕ × (Fin 6 → ℝ)) × ℝ | zS p.stage.b p.stage.N r x = q ∧
        ⌊(if h then eval (exS p.stage.b x.1 x.2) p.stage.P else (exS p.stage.b x.1 x.2) 3) /
          p.stage.N ^ (-s)⌋ = a} ⊆ p.cellSet r s q a univ := by
      intro x hx
      rw [← p.cellSet_eq r s q a univ h]
      exact ⟨hx.1, hx.2, trivial⟩
    calc _ ≤ p.synth.mu (p.cellSet r s q a univ) := measure_mono hsub
      _ ≤ ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) * U {u | p.synth.β * u ∈ univ} :=
          p.cap_model r s hs1 hsn q a MeasurableSet.univ
      _ = ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) := by simp [U]
  · set V : Set ℝ := {w : ℝ | ⌊w / p.sN ^ (-v)⌋ = v₀} with hV
    have hVm : MeasurableSet V :=
      measurableSet_eq_fun (Int.measurable_floor.comp (measurable_id.div_const _)) measurable_const
    have hsub : {x : (ℕ × (Fin 6 → ℝ)) × ℝ | zS p.stage.b p.stage.N r x = q ∧
        ⌊(if h then eval (exS p.stage.b x.1 x.2) p.stage.P else (exS p.stage.b x.1 x.2) 3) /
          p.stage.N ^ (-s)⌋ = a ∧ ⌊p.stage.b x.1 3 / p.stage.N ^ (-v)⌋ = v₀} ⊆
        p.cellSet r s q a V := by
      intro x hx
      rw [← p.cellSet_eq r s q a V h]
      exact hx
    calc _ ≤ p.synth.mu (p.cellSet r s q a V) := measure_mono hsub
      _ ≤ ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) * U {u | p.synth.β * u ∈ V} :=
          p.cap_model r s hs1 hsn q a hVm
      _ = ENNReal.ofReal (p.sK * p.sN ^ (-3 * r - p.d₁ * s)) * p.synth.pal V := by
          rw [p.synth.pal_apply hVm]

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
