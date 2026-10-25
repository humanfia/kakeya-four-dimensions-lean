import Submission.Obl.k4_general_parent_projected_layers.Worlds
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-!
# Scalar's input from small losses

Scalar's input with its fixed-power bounds on the density parameter `c`, from bounds
with a small loss `N^δ`: the lower bound on `c` comes from the unit cap and the dense
mass, the upper one from the nonempty terminal support. No floor on the prior is used.

The counting in `readiness_unit_cap_mass` and the two parameter bounds are adapted
from session x0774's o222 file
`Submission/Obl/k4_projected_parent_contact_reduction/ScalarParameterBounds.lean`
(branch `x0774` of o222), renamed to avoid clashes.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery (scalarY scalarX scalarCell)
open Submission.Obl.k4_horizontal_supercritical_three_projections
  (chartLaw chartLaw_domination chartLaw_time_support)

noncomputable section

/-- A unit-thickness cap bounds the total mass of a law with bounded coordinates.
(Adapted from x0774's `scalar_unit_cap_mass`, o222.) -/
theorem readiness_unit_cap_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (time y x : Ω → ℝ) {sigma A L c : ℝ}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hA : 0 ≤ A) (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hbound : ∀ᵐ p ∂μ, |time p| ≤ 1 ∧ |y p| ≤ L ∧ |x p| ≤ L)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | (![⌊time p / sigma⌋, ⌊y p / sigma⌋, ⌊x p⌋] : Fin 3 → ℤ) = q} ≤
        ENNReal.ofReal (A * sigma ^ 2 * c)) :
    μ univ ≤ ENNReal.ofReal (216 * A * L ^ 2 * c) := by
  classical
  have hL0 : 0 ≤ L := (zero_le_one : (0 : ℝ) ≤ 1).trans hL
  obtain ⟨Ft, hFt, htime⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hs (by norm_num : (0 : ℝ) ≤ 1) 0
  obtain ⟨Fy, hFy, hy⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hs hL0 0
  obtain ⟨Fx, hFx, hx⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover (by norm_num : (0 : ℝ) < 1) hL0 0
  let Q : Fin 3 → Finset ℤ := ![Ft, Fy, Fx]
  let F := Fintype.piFinset Q
  let code : Ω → Fin 3 → ℤ := fun p => ![⌊time p / sigma⌋, ⌊y p / sigma⌋, ⌊x p⌋]
  have hcover : ∀ᵐ p ∂μ, code p ∈ F := by
    filter_upwards [hbound] with p hp
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · show ⌊time p / sigma⌋ ∈ Ft
      exact htime _ (by simpa only [sub_zero] using hp.1)
    · show ⌊y p / sigma⌋ ∈ Fy
      exact hy _ (by simpa only [sub_zero] using hp.2.1)
    · show ⌊x p⌋ ∈ Fx
      simpa only [div_one] using hx (x p) (by simpa only [sub_zero] using hp.2.2)
  have htarea : (Ft.card : ℝ) * sigma ≤ 6 := by
    have h := mul_le_mul_of_nonneg_right hFt hs.le
    have heq : (4 * (1 : ℝ) / sigma + 2) * sigma = 4 + 2 * sigma := by field_simp
    rw [heq] at h
    linarith
  have hyarea : (Fy.card : ℝ) * sigma ≤ 6 * L := by
    have h := mul_le_mul_of_nonneg_right hFy hs.le
    have heq : (4 * L / sigma + 2) * sigma = 4 * L + 2 * sigma := by field_simp
    rw [heq] at h
    linarith
  have hxarea : (Fx.card : ℝ) ≤ 6 * L := by
    simp only [div_one] at hFx
    linarith
  have hcard : (F.card : ℝ) * sigma ^ 2 ≤ 216 * L ^ 2 := by
    have hprod : (F.card : ℝ) = (Ft.card : ℝ) * (Fy.card : ℝ) * (Fx.card : ℝ) := by
      simp [F, Q, Fintype.card_piFinset, Fin.prod_univ_three]
    calc
      _ = ((Ft.card : ℝ) * sigma) * ((Fy.card : ℝ) * sigma) * (Fx.card : ℝ) := by
        rw [hprod]; ring
      _ ≤ 6 * (6 * L) * (6 * L) := mul_le_mul
        (mul_le_mul htarea hyarea (by positivity) (by norm_num)) hxarea
        (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hsub : univ ≤ᵐ[μ] ⋃ q ∈ F, {p | code p = q} := by
    filter_upwards [hcover] with p hp
    intro _
    exact mem_iUnion.mpr ⟨code p, mem_iUnion.mpr ⟨hp, rfl⟩⟩
  calc
    _ ≤ μ (⋃ q ∈ F, {p | code p = q}) := measure_mono_ae hsub
    _ ≤ ∑ q ∈ F, μ {p | code p = q} := measure_biUnion_finset_le F _
    _ ≤ ∑ _q ∈ F, ENNReal.ofReal (A * sigma ^ 2 * c) :=
      Finset.sum_le_sum (fun q _ => hcap q)
    _ = ENNReal.ofReal ((F.card : ℝ) * (A * sigma ^ 2 * c)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ = (A * c) * ((F.card : ℝ) * sigma ^ 2) := by ring
        _ ≤ (A * c) * (216 * L ^ 2) := mul_le_mul_of_nonneg_left hcard (mul_nonneg hA hc)
        _ = _ := by ring)

/-- The nonempty terminal support forces the upper parameter bound.
(Adapted from x0774's `scalar_parameter_upper`, o222.) -/
theorem readiness_param_upper {β : Type*} (F : Finset β) {sigma H a c d : ℝ}
    (hF : F.Nonempty) (hs : 0 < sigma) (hc : 0 < c)
    (hsupport : (F.card : ℝ) * sigma ^ 2 ≤ H * c⁻¹ * a ^ (-d)) :
    c ≤ H * a ^ (-d) / sigma ^ 2 := by
  have hcard : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.one_le_card.mpr hF
  have hbase : sigma ^ 2 ≤ H * c⁻¹ * a ^ (-d) :=
    (by nlinarith [sq_nonneg sigma] : sigma ^ 2 ≤ (F.card : ℝ) * sigma ^ 2).trans hsupport
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  have h := mul_le_mul_of_nonneg_right hbase hc.le
  have heq : (H * c⁻¹ * a ^ (-d)) * c = H * a ^ (-d) := by field_simp [hc.ne']
  rw [heq] at h
  nlinarith

/-- Scalar's input at loss exponent `η`, with `C = 2M + s + 2`, from bounds with the
smaller loss `N^δ`, `10 δ ≤ η`. The density parameter `c` needs no a priori bounds. -/
theorem scalarInput_of_small_loss {α : Type} [MeasurableSpace α]
    {N η δ d s M c : ℝ} {ν : Measure α} {μ : Measure (α × ℝ)} {b : α → Fin 5 → ℝ}
    (hN : 2 ≤ N) (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hsM : s < M) (hc : 0 ≤ c)
    (hδ : 0 < δ) (hδη : 10 * δ ≤ η) (hδ1 : δ ≤ 1 / 100) (h1944 : 1944 ≤ N ^ δ)
    (hb : Measurable b) (hν : IsProbabilityMeasure ν)
    (hdom : μ ≤ ENNReal.ofReal (N ^ δ) • (ν.prod volume))
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcoeff : ∀ l i, |b l i| ≤ N ^ δ)
    (hmass : ENNReal.ofReal (N ^ (-δ)) ≤ μ univ)
    (hcap : ∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
      μ {p | scalarCell (b p.1) p.2 (N ^ (-M)) = q ∧
        ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
          ENNReal.ofReal (N ^ δ * (N ^ (-M)) ^ 2 * c * (N ^ (-r)) ^ d))
    (hsupport : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      c * ((F.card : ℝ) * (N ^ (-M)) ^ 2) * (N ^ (-s)) ^ d ≤ N ^ (3 * δ) ∧
      ∀ᵐ p ∂μ, (scalarCell (b p.1) p.2 (N ^ (-M)),
        ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F) :
    ScalarInput N η d s M (2 * M + s + 2) c ν μ b ∧ ENNReal.ofReal (N ^ (-η)) ≤ μ univ := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hM : 0 < M := hs.trans hsM
  set σ := N ^ (-M) with hσdef
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN0 _
  have hσ1 : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hpδ : 0 < N ^ δ := Real.rpow_pos_of_pos hN0 δ
  have hpδ1 : 1 ≤ N ^ δ := Real.one_le_rpow hN1 hδ.le
  have hδη' : N ^ δ ≤ N ^ η := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3δη : N ^ (3 * δ) ≤ N ^ η := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- incidences live at unit times
  have htime_ae : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    refine measure_mono_null ?_ htime
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    simp only [mem_compl_iff, mem_prod, mem_univ, true_and]
    exact hp
  -- the lower bound on `c`, from the unit cap and the dense mass
  have hmass_le : μ univ ≤ ENNReal.ofReal (216 * N ^ δ * (3 * N ^ δ) ^ 2 * c) := by
    apply readiness_unit_cap_mass μ (fun p => p.2) (fun p => scalarY (b p.1) p.2)
      (fun p => scalarX (b p.1) p.2) hσ hσ1 hpδ.le (by linarith) hc
    · filter_upwards [htime_ae] with p hp
      obtain ⟨ht0, ht1⟩ := hp
      have hb0 := hcoeff p.1 0
      have hb1 := hcoeff p.1 1
      have hb2 := hcoeff p.1 2
      have hb3 := hcoeff p.1 3
      have hb4 := hcoeff p.1 4
      have ht : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have ht2 : |p.2 ^ 2| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht
      refine ⟨ht, ?_, ?_⟩
      · simp only [scalarY]
        calc |b p.1 0 + p.2 * b p.1 1| ≤ |b p.1 0| + |p.2| * |b p.1 1| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ N ^ δ + 1 * N ^ δ := by gcongr
          _ ≤ 3 * N ^ δ := by linarith
      · simp only [scalarX]
        calc |b p.1 2 + p.2 * b p.1 3 + p.2 ^ 2 * b p.1 4|
            ≤ |b p.1 2| + |p.2| * |b p.1 3| + |p.2 ^ 2| * |b p.1 4| := by
              rw [← abs_mul, ← abs_mul]
              exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ N ^ δ + 1 * N ^ δ + 1 * N ^ δ := by gcongr
          _ = 3 * N ^ δ := by ring
    · intro q
      refine le_trans (measure_mono ?_) ((hcap 0 ![q 0, q 1] (q 2) le_rfl hs.le).trans ?_)
      · intro p hp
        simp only [Set.mem_ofPred_eq] at hp ⊢
        refine ⟨?_, ?_⟩
        · ext i
          fin_cases i
          · simpa [scalarCell] using congrFun hp 0
          · simpa [scalarCell] using congrFun hp 1
        · simpa using congrFun hp 2
      · simp
  have hcN : N ^ (-δ) ≤ 1944 * N ^ (3 * δ) * c := by
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hmass_le)
    have h3 : N ^ (3 * δ) = N ^ δ * N ^ δ * N ^ δ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
    rw [h3]; nlinarith
  have hc5 : N ^ (-(5 * δ)) ≤ c := by
    have h4 : N ^ (-δ) ≤ N ^ (4 * δ) * c := by
      have : 1944 * N ^ (3 * δ) * c ≤ N ^ δ * N ^ (3 * δ) * c := by gcongr
      have h44 : N ^ δ * N ^ (3 * δ) = N ^ (4 * δ) := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [h44] at this
      linarith
    have hsplit : N ^ (-(5 * δ)) = N ^ (-δ) * N ^ (-(4 * δ)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hinv : N ^ (4 * δ) * N ^ (-(4 * δ)) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    rw [hsplit]
    calc N ^ (-δ) * N ^ (-(4 * δ)) ≤ N ^ (4 * δ) * c * N ^ (-(4 * δ)) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hN0.le _)
      _ = c * (N ^ (4 * δ) * N ^ (-(4 * δ))) := by ring
      _ = c := by rw [hinv, mul_one]
  have hc_lower : N ^ (-(2 * M + s + 2)) ≤ c :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hc5
  have hc0 : 0 < c := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hc5
  -- the upper bound on `c`, from the nonempty terminal support
  obtain ⟨F, hFcard₀, hFae⟩ := hsupport
  have hFcard : (F.card : ℝ) * σ ^ 2 ≤ N ^ (3 * δ) * c⁻¹ * (N ^ (-s)) ^ (-d) := by
    have has : 0 < (N ^ (-s)) ^ d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
    rw [Real.rpow_neg (Real.rpow_nonneg hN0.le _), mul_assoc, ← mul_inv,
      le_mul_inv_iff₀ (mul_pos hc0 has)]
    calc (F.card : ℝ) * σ ^ 2 * (c * (N ^ (-s)) ^ d)
        = c * ((F.card : ℝ) * σ ^ 2) * (N ^ (-s)) ^ d := by ring
      _ ≤ N ^ (3 * δ) := hFcard₀
  have hF : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hF0
    subst hF0
    have hfalse : ∀ᵐ p ∂μ, False := hFae.mono fun p hp => by simp at hp
    have hμ0 : μ = 0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse)
    have hpos : 0 < ENNReal.ofReal (N ^ (-δ)) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN0 _)
    rw [hμ0, Measure.coe_zero, Pi.zero_apply] at hmass
    exact absurd hmass (not_le.mpr hpos)
  have hcup := readiness_param_upper F hF hσ hc0 hFcard
  have hc_upper : c ≤ N ^ (2 * M + s + 2) := by
    refine hcup.trans ?_
    have hσ2 : σ ^ 2 = N ^ (-(2 * M)) := by
      rw [hσdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have has : (N ^ (-s)) ^ (-d) = N ^ (s * d) := by
      rw [← Real.rpow_mul hN0.le]; ring_nf
    rw [hσ2, has, div_eq_mul_inv, ← Real.rpow_neg hN0.le, neg_neg, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hsd : s * d ≤ s := by nlinarith
    linarith
  refine ⟨⟨hb, hν, ?_, htime, fun l i => (hcoeff l i).trans hδη', hc_lower, hc_upper, ?_,
    ⟨F, hFcard.trans ?_, hFae⟩⟩, ?_⟩
  · refine hdom.trans ?_
    intro E
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  · intro r q j hr hrs
    refine (hcap r q j hr hrs).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  · gcongr
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- A world is ready once its crop geometry and the small-loss bounds of its conditioned
current law hold; the conditioned prior, domination and time support are derived. -/
theorem ScalarWorld.ready_of_small_loss {α : Type} [MeasurableSpace α] (w : ScalarWorld α)
    {N η δ d s M χ g K : ℝ} {b : α → Fin 6 → ℝ} {P : MvPolynomial (Fin 4) ℝ}
    {ν : Measure α} [IsProbabilityMeasure ν] {π : Measure ℝ} {ζ : Measure (α × ℝ)}
    (hN : 2 ≤ N) (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hsM : s < M)
    (hδ : 0 < δ) (hδη : 10 * δ ≤ η) (hδ1 : δ ≤ 1 / 100) (h1944 : 1944 ≤ N ^ δ)
    (hχ : 0 ≤ χ) (hg : 0 ≤ g)
    (hcrop : MeasurableSet w.crop) (hprior : ν w.crop ≠ 0)
    (htags : ∀ l ∈ w.crop, ⌊b l 3 / χ⌋ = w.tag 0 ∧ ⌊b l 0 / χ⌋ = w.tag 1)
    (hcenter : |w.y₀| + |w.y₁| ≤ K)
    (hy : ∀ l ∈ w.crop, ∀ t : ℝ, scalarY (w.coeff l) t =
      ((Submission.Lib.K4ContactNormalization.point (b l) t) 2 - w.y₀ - t * w.y₁) / g)
    (hx : ∀ l ∈ w.crop, ∀ t : ℝ, scalarX (w.coeff l) t =
      MvPolynomial.eval (Submission.Lib.K4ContactNormalization.point (b l) t) P)
    (hcoeffm : Measurable w.coeff)
    (hζdom : ζ ≤ ENNReal.ofReal (N ^ δ) • (ν.prod volume))
    (hζtime : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcoeff : ∀ l i, |w.coeff l i| ≤ N ^ δ)
    (hmass : ENNReal.ofReal (N ^ (-δ)) ≤ chartLaw ν ζ w.crop univ)
    (hcap : ∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
      chartLaw ν ζ w.crop {p | scalarCell (w.coeff p.1) p.2 (N ^ (-M)) = q ∧
        ⌊scalarX (w.coeff p.1) p.2 / N ^ (-r)⌋ = j} ≤
          ENNReal.ofReal (N ^ δ * (N ^ (-M)) ^ 2 * w.param χ g ν π * (N ^ (-r)) ^ d))
    (hsupport : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      w.param χ g ν π * ((F.card : ℝ) * (N ^ (-M)) ^ 2) * (N ^ (-s)) ^ d ≤ N ^ (3 * δ) ∧
      ∀ᵐ p ∂chartLaw ν ζ w.crop, (scalarCell (w.coeff p.1) p.2 (N ^ (-M)),
        ⌊scalarX (w.coeff p.1) p.2 / N ^ (-s)⌋) ∈ F) :
    w.Ready N η d s M (2 * M + s + 2) χ g K b P ν π ζ := by
  have hparam : 0 ≤ w.param χ g ν π := by
    unfold ScalarWorld.param
    exact div_nonneg (mul_nonneg (mul_nonneg hχ hg) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  obtain ⟨hinput, hdense⟩ := scalarInput_of_small_loss hN hd hd1 hs hsM hparam hδ hδη hδ1 h1944
    hcoeffm (ProbabilityTheory.cond_isProbabilityMeasure hprior)
    (chartLaw_domination ν ζ w.crop _ hζdom) (chartLaw_time_support ν ζ w.crop hζtime)
    hcoeff hmass hcap hsupport
  exact ⟨hcrop, hprior, htags, hcenter, hy, hx, hinput, hdense⟩

end

end Submission.Obl.k4_general_parent_projected_layers
