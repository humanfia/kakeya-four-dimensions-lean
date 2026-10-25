/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeCellLists.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarContactCount
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeTimeLists
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectedBaseline

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- One original terminal incidence with its named original coarse ancestor. -/
def namedNativeIncidence (cfg : Data α) (k : ℕ) (s₀ s : ℝ)
    (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
    (p : α × ℝ) (z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k s)) : Prop :=
  ∃ ip : Fin (cfg.n k s₀), choice z.1 = some ip ∧ cfg.j k s₀ ip = z.1 ∧
    p.1 ∈ cfg.B k s₀ ip ∧ p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ ip) ∧
    p.1 ∈ cfg.B k s z.2 ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s z.2) ∧
    cfg.A k s z.2 ⊆ cfg.A k s₀ ip ∧
    I (cfg.T k s) (cfg.j k s z.2) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)

/-- Keep every terminal entry with a genuine retained contact in this scalar
cell, recording its coarse block so the named ancestor remains unambiguous. -/
def nativeCellEntries (cfg : Data α) (k : ℕ) (s₀ s D σ : ℝ) (P Q : ℤ)
    (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
    (E : Set (α × ℝ)) (c : Fin 2 → ℤ) :
    Finset (Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k s)) := by
  classical
  exact Finset.univ.filter fun z => ∃ p ∈ E,
    chartCell D σ P Q (cfg.b k p.1) p.2 = c ∧ cfg.namedNativeIncidence k s₀ s choice p z

theorem mem_nativeCellEntries {k : ℕ} {s₀ s D σ : ℝ} {P Q : ℤ}
    {choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀))}
    {E : Set (α × ℝ)} {c : Fin 2 → ℤ}
    {z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k s)} :
    z ∈ cfg.nativeCellEntries k s₀ s D σ P Q choice E c ↔
      ∃ p ∈ E, chartCell D σ P Q (cfg.b k p.1) p.2 = c ∧
        cfg.namedNativeIncidence k s₀ s choice p z := by
  classical
  simp only [nativeCellEntries, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every scalar cell has a uniformly short actual native list. All counting
uses whole original native witnesses, even when the retained contact has no
quantitative mass. -/
theorem Prepared.eventually_native_cell_list_count (h : cfg.Prepared)
    {s₀ s M ε : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
      (P Q V : ℤ)
      (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
      (E : Set (α × ℝ)),
      |(P : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀))| ≤ 3 * cfg.K k →
      |(V : ℝ) * cfg.N k ^ (-M)| ≤ 3 * cfg.K k →
      (∀ p ∈ E,
        ⌊cfg.b k p.1 0 / cfg.N k ^ (-(2 * cfg.κ * s₀))⌋ = P ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋ = V ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-M)) →
      ∀ c : Fin 2 → ℤ,
        ((cfg.nativeCellEntries k s₀ s (cfg.N k ^ (-(2 * cfg.κ * s₀)))
          (cfg.N k ^ (-(20 * s₀))) P Q choice E c).card : ℝ) ≤
          81 * cfg.N k ^ ε *
            (cfg.N k ^ (-s₀) / cfg.N k ^ (-s)) ^ cfg.d := by
  filter_upwards [h.eventually_scalar_contact_count hs₀ hs hnear hM hε,
    h.eventually_scalar_contact_margins hs₀ hs hnear hM,
    h.eventually_scalar_contact_margins hs₀ le_rfl (by
      have hm : 0 < min cfg.κ (1 - 2 * cfg.κ) :=
        lt_min h.rate_pos (by linarith [h.subcritical_rate])
      simpa only [sub_self] using (show 0 ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16 by positivity))
      hM] with k hcount hmargin hmargin₀
  intro parent child P Q V choice E hpc hv hE c
  classical
  let D := cfg.N k ^ (-(2 * cfg.κ * s₀))
  let σ := cfg.N k ^ (-(20 * s₀))
  let χ := cfg.N k ^ (-M)
  let S := cfg.nativeCellEntries k s₀ s D σ P Q choice E c
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hD : 0 < D := Real.rpow_pos_of_pos hN _
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN _
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hcode (p : α × ℝ) (hp : chartCell D σ P Q (cfg.b k p.1) p.2 = c) :
      |p.2 - σ * (c 0 : ℝ)| ≤ σ ∧
      |chartR D P Q (cfg.b k p.1) p.2 - σ * (c 1 : ℝ)| ≤ σ := by
    have ht := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hσ p.2
    have hR := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hσ
      (chartR D P Q (cfg.b k p.1) p.2)
    have he₀ := congrFun hp 0
    have he₁ := congrFun hp 1
    simp only [chartCell, Matrix.cons_val_zero, Matrix.cons_val_one] at he₀ he₁
    exact ⟨by simpa only [he₀] using ht, by simpa only [he₁] using hR⟩
  apply (card_list_of_contact_time_blocks S (cfg.T k s₀) (cfg.T k s)
    Prod.fst (fun z => cfg.j k s z.2) (τ := σ * (c 0 : ℝ))
    (L := cfg.N k ^ ε * (cfg.N k ^ (-s₀) / cfg.N k ^ (-s)) ^ cfg.d) hσ.le
    (hmargin₀ parent.assignments).1 (hmargin child.assignments).1
    (by positivity) ?_ ?_).trans_eq (by ring)
  · intro z hz
    obtain ⟨p, hpE, hpcode, ip, hip, hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ :=
      mem_nativeCellEntries.mp hz
    exact ⟨p.2, (hcode p hpcode).1, by simpa only [hjp] using ht₀, htc⟩
  · intro j₀ j
    let F := S.filter fun z => z.1 = j₀ ∧ cfg.j k s z.2 = j
    cases hchoice : choice j₀ with
    | none =>
      have hF : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hzS, hz₀, hzj⟩ := Finset.mem_filter.mp hz
        obtain ⟨p, hpE, hpcode, ip, hip, _⟩ := mem_nativeCellEntries.mp hzS
        rw [hz₀, hchoice] at hip
        contradiction
      change (F.card : ℝ) ≤ _
      rw [hF, Finset.card_empty, Nat.cast_zero]
      positivity
    | some ip =>
      let Ic := F.image Prod.snd
      have hFc : F.card = Ic.card := by
        symm
        apply Finset.card_image_of_injOn
        intro z hz z' hz' he
        exact Prod.ext ((Finset.mem_filter.mp hz).2.1.trans
          (Finset.mem_filter.mp hz').2.1.symm) he
      change (F.card : ℝ) ≤ _
      rw [hFc]
      apply hcount parent child ip Ic j ((P : ℝ) * D) ((Q : ℝ) * D)
        ((V : ℝ) * χ) (σ * (c 1 : ℝ)) hpc hv
      · intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hz).2.2
      · intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨p, hpE, hpcode, ip', hip', hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ :=
          mem_nativeCellEntries.mp (Finset.mem_filter.mp hz).1
        have he : ip' = ip := by
          rw [(Finset.mem_filter.mp hz).2.1, hchoice] at hip'
          exact Option.some.inj hip'.symm
        simpa only [he] using hA
      · intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨p, hpE, hpcode, ip', hip', hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ :=
          mem_nativeCellEntries.mp (Finset.mem_filter.mp hz).1
        have he : ip' = ip := by
          rw [(Finset.mem_filter.mp hz).2.1, hchoice] at hip'
          exact Option.some.inj hip'.symm
        simpa only [he] using hI
      · intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨p, hpE, hpcode, ip', hip', hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ :=
          mem_nativeCellEntries.mp (Finset.mem_filter.mp hz).1
        have hp := normalized_parameter_mem_unit hD (hE p hpE).1
        have hvel := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hχ
          (cfg.b k p.1 3)
        rw [(hE p hpE).2.1] at hvel
        refine ⟨p.1, p.2, hpc, htc, ?_, ?_, (hE p hpE).2.2, ?_⟩
        · rw [abs_of_nonneg (show 0 ≤ cfg.b k p.1 0 - (P : ℝ) * D by
            simpa only [zero_mul] using (le_div_iff₀ hD).mp hp.1)]
          exact (div_le_one hD).mp hp.2
        · simpa only [mul_comm] using hvel
        · exact (hcode p hpcode).2

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
