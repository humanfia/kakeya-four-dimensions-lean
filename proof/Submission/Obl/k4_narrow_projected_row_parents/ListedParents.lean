import Submission.Obl.k4_narrow_projected_row_parents.DeepCover
import Submission.Obl.k4_narrow_projected_row_parents.PaletteControl
import Submission.Obl.k4_narrow_projected_row_parents.Growth
import Submission.Obl.k4_critical_affine_derivative_preparation.CriticalScales
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Listed parents at one scale yield row parents. All hypotheses concerning
the deeper labels and the palette separation follow from the original atlas. -/
theorem rowParents_of_parentLists (hRow : Row) (cfg : Model α) (hv : Model.Valid cfg)
    {r r' e aξ : ℝ} (hr : 0 < r) (hrr' : r < r') (hr'U : r' ≤ cfg.U)
    (he : 0 < e) (heξ : e < aξ)
    (hmajor : aξ < cfg.κ * (r' - r)) (hminor : e < cfg.ℓ * (r' - r))
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k) (hMsub : Model.Subpow cfg.N M)
    (hfreq : ∃ᶠ k in atTop, Nonempty
      (ParentLists (Model.parameters cfg) (Model.prepared cfg) k r
        (cfg.N k ^ (-aξ)) (cfg.N k ^ (-e)) (M k))) :
    RowParents cfg r := by
  have haξ : 0 < aξ := he.trans heξ
  let p := Model.parameters cfg
  let a := Model.prepared cfg
  have hp : p.Valid := Model.parameters_valid hv
  have hav : a.Valid p := Model.prepared_valid hv
  have hcommon : a.Common p := hav.1
  have hN : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hv.scale k]
  have hNp : ∀ k, 0 < cfg.N k := fun k => by linarith [hv.scale k]
  obtain ⟨C, hC, hCsub, hCgood⟩ := exists_palette_control cfg hv M hM hMsub haξ
  let M' : ℕ → ℝ := fun k => rowReadyBound (M k) (C k) (cfg.K k)
  have hM' : ∀ k, 1 ≤ M' k := by
    intro k
    have hm : 0 ≤ M k := zero_le_one.trans (hM k)
    have hc : 0 ≤ C k := zero_le_one.trans (hC k)
    have hk : 0 ≤ cfg.K k := zero_le_one.trans (hv.subpower.1 k)
    have h1 : 0 ≤ 3 * (2 * C k) ^ 2 * (M k + 1) := by positivity
    have h2 : 0 ≤ C k ^ 2 *
        (12 * C k ^ 2 * (4 + C k + 3 * (2 * C k) ^ 2 * (M k + 1)) + 2) ^ 2 /
        ((1 / (18 * M k * cfg.K k)) ^ 2 / 2) := by positivity
    dsimp [M', rowReadyBound]
    linarith [hM k]
  have hM'sub : Model.Subpow cfg.N M' :=
    rowReadyBound_subpow hN hv.scale_limit hM hC hv.subpower.1 hMsub hCsub hv.subpower.2
  let R : ℝ := 2 + |r⁻¹| + |r'| + |aξ| + |aξ⁻¹|
  have hR : 1 < R := by
    dsimp [R]
    linarith [abs_nonneg r⁻¹, abs_nonneg r', abs_nonneg aξ, abs_nonneg aξ⁻¹]
  have hRp : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ hr hRp).mp
    dsimp [R]
    linarith [le_abs_self r⁻¹, abs_nonneg r', abs_nonneg aξ, abs_nonneg aξ⁻¹]
  have hRr' : r' ≤ R := by
    dsimp [R]
    linarith [le_abs_self r', abs_nonneg r⁻¹, abs_nonneg aξ, abs_nonneg aξ⁻¹]
  have hRξ : R⁻¹ ≤ aξ := by
    apply (inv_le_comm₀ haξ hRp).mp
    dsimp [R]
    linarith [le_abs_self aξ⁻¹, abs_nonneg r⁻¹, abs_nonneg r', abs_nonneg aξ]
  have hξR : aξ ≤ R := by
    dsimp [R]
    linarith [le_abs_self aξ, abs_nonneg r⁻¹, abs_nonneg r', abs_nonneg aξ⁻¹]
  have hqev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hv.scale_limit hv.subpower.1 hv.subpower.2 3
    (a := -cfg.κ * (r' - r)) (b := -aξ) (by linarith) (A := 2) (by norm_num)
  have hgev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hv.scale_limit hv.subpower.1 hv.subpower.2 1
    (a := -cfg.ℓ * (r' - r)) (b := -e) (by linarith) (A := 1) (by norm_num)
  have hready : ∀ᶠ k in atTop,
      ParentLists p a k r (cfg.N k ^ (-aξ)) (cfg.N k ^ (-e)) (M k) →
        Nonempty (RowReady p a k r (cfg.N k ^ (-aξ)) (cfg.N k ^ (-e)) (M' k)) := by
    filter_upwards [hav.2.2.1 R hR, hav.2.2.2 R hR, hCgood, hqev, hgev]
      with k hatlas hnest hCk hqk hgk
    intro PL
    have hAp : a.AtlasAt p R k r := hatlas r hRr (hrr'.le.trans hr'U)
    have hAd : a.AtlasAt p R k r' := hatlas r' (hRr.trans hrr'.le) hr'U
    have hnest' := hnest r r' hRr hrr' hr'U
    have hKp : 0 < cfg.K k := lt_of_lt_of_le zero_lt_one (hv.subpower.1 k)
    have hq : 0 < a.q k r := q_pos a k r
    have hq' : 0 < a.q k r' := q_pos a k r'
    have hξ : 0 < cfg.N k ^ (-aξ) := Real.rpow_pos_of_pos (hNp k) _
    have hE : 0 < cfg.N k ^ (-e) := Real.rpow_pos_of_pos (hNp k) _
    have hξE : cfg.N k ^ (-aξ) ≤ cfg.N k ^ (-e) :=
      Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
    have hE1 : cfg.N k ^ (-e) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN k) (by linarith)
    have htime := Submission.Obl.k4_critical_affine_derivative_preparation.time_length_comparison
      (hNp k) hKp hAp.1 hAp.2.1
    have htime' := Submission.Obl.k4_critical_affine_derivative_preparation.time_length_comparison
      (hNp k) hKp hAd.1 hAd.2.1
    have hqd : a.q k r' ≤ cfg.K k * cfg.N k ^ (-cfg.κ * r') := by
      have ht : a.q k r' / cfg.K k ≤ cfg.N k ^ (-cfg.κ * r') := by
        simpa only [PreparedModel.q, zpow_neg, zpow_natCast, p, Model.parameters] using htime'.1
      exact ((div_le_iff₀ hKp).mp ht).trans_eq (mul_comm _ _)
    have hqp : cfg.N k ^ (-cfg.κ * r) / cfg.K k ≤ a.q k r := by
      apply (div_le_iff₀ hKp).mpr
      simpa only [PreparedModel.q, zpow_neg, zpow_natCast, mul_comm, p, Model.parameters] using htime.2
    have hsmall : 2 * cfg.K k * a.q k r' ≤ cfg.N k ^ (-aξ) * a.q k r := by
      calc 2 * cfg.K k * a.q k r'
          ≤ 2 * cfg.K k * (cfg.K k * cfg.N k ^ (-cfg.κ * r')) := by gcongr
        _ = (2 * cfg.K k ^ 3 * cfg.N k ^ (-cfg.κ * (r' - r))) *
              (cfg.N k ^ (-cfg.κ * r) / cfg.K k) := by
          rw [div_eq_mul_inv]
          have hid : cfg.N k ^ (-cfg.κ * (r' - r)) * cfg.N k ^ (-cfg.κ * r) =
              cfg.N k ^ (-cfg.κ * r') := by
            rw [← Real.rpow_add (hNp k)]; congr 1; ring
          calc _ = 2 * cfg.K k ^ 2 * cfg.N k ^ (-cfg.κ * r') := by ring
            _ = 2 * cfg.K k ^ 2 *
                (cfg.N k ^ (-cfg.κ * (r' - r)) * cfg.N k ^ (-cfg.κ * r)) := by rw [hid]
            _ = _ := by field_simp
        _ ≤ cfg.N k ^ (-aξ) * (cfg.N k ^ (-cfg.κ * r) / cfg.K k) :=
          mul_le_mul_of_nonneg_right hqk.le (by positivity [hNp k])
        _ ≤ cfg.N k ^ (-aξ) * a.q k r := mul_le_mul_of_nonneg_left hqp hξ.le
    have hsmall' : a.q k r' ≤ cfg.N k ^ (-aξ) * a.q k r := by
      apply le_trans _ hsmall
      nlinarith [hv.subpower.1 k]
    have he₁ : cfg.K k * narrow p k r' / narrow p k r ≤ cfg.N k ^ (-e) := by
      have hid : cfg.K k * narrow p k r' / narrow p k r =
          cfg.K k * cfg.N k ^ (-cfg.ℓ * (r' - r)) := by
        dsimp [narrow, p, Model.parameters]
        rw [mul_div_assoc, ← Real.rpow_sub (hNp k)]
        congr 2
        ring
      rw [hid]
      simpa only [pow_one, one_mul] using hgk.le
    have hcover := ae_deepGood_cover p a k hcommon hAp hAd hnest' PL.Q
    have hcoverW : a.rho k {z | z ∈ PL.W ∧ ¬ ∃ n, deepGood a k r r' PL.Q n ∧
        z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n} = 0 := by
      have h : ∀ᵐ z ∂a.rho k, z ∈ PL.W → ∃ n, deepGood a k r r' PL.Q n ∧
          z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n :=
        hcover.mono fun z hz hW => hz (PL.W_sub hW).1 (PL.W_sub hW).2
      simpa only [ae_iff, not_imp] using h
    exact rowReady_of_parentLists p hp a k PL hξ hξE hE1 (hM k) hCk.1 hCk.2.1
      (hcommon k).1 (hcommon k).2.2.2.2.1 (a.incidence_finite p hcommon k)
      (hcommon k).2.2.1 (hcommon k).2.1
      (fun n => (hAd.2.2.1 n).1) (fun n => (hAd.2.2.1 n).2.1)
      (fun n => (hAd.2.2.1 n).2.2) hAd.2.2.2.1
      (fun n => (hAd.2.2.2.2.1 n).2.2.2.1 1)
      (fun n l hl t ht => let h := (hAd.2.2.2.2.1 n).2.2.2.2.2.1 l hl t ht;
        ⟨h.1, h.2.2⟩)
      (fun n v₀ => hAd.2.2.2.2.2.2 n aξ v₀ hRξ hξR)
      hcoverW hsmall hsmall' he₁ hCk.2.2
  apply rowParents_of_rowReady hRow cfg hv he heξ M' hM' hM'sub
  exact (hfreq.and_eventually hready).mono fun k ⟨⟨PL⟩, hk⟩ => hk PL

end Submission.Obl.k4_narrow_projected_row_parents
