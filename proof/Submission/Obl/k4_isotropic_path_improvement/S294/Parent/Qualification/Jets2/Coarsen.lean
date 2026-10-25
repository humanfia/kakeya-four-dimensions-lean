-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Coarsen, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Coarsen.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Coarsen.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Coarsen.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Cover

set_option autoImplicit false

/-!
# Coarsening a list, version 2 (deterministic replacement of `a04:entropy-independence`)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`,
`Jets/Coarsen.lean` (`coarsen_lists`), with the planar square cover replaced by the cube cover of
`Jets2/Cover.lean`.

Fix a time `t`.  Suppose a quantity `J` of the labelled trajectories of a set `D` is determined,
at width `w`, by the fine scalar bin `⌊S/q⌋` up to `Kf` values, and is `CJ r`-Lipschitz inside a
coefficient piece of scale `r ≥ q`.  Then outside a set of prior mass
`≤ 4800 K³ (CJ r / w + 1) / Kpop`, it is determined by the *coarse* scalar bin `⌊S/r⌋` up to
`3 K Kf Kpop` values: keep, in each coarse bin, the values listed by at least
`(r/q)^d / Kpop` of its occupied fine bins.  A value listed by fewer fine bins can only be taken
by trajectories whose fine scalar bins are few among the `≈ (r/q)^d` fine bins that the
conditional cap `BC` spreads every coefficient piece over.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- **Coarsening a fine list.** -/
theorem coarsen_lists {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d)
    (t q r w : ℝ) (hζq : ζ ≤ q) (hqr : q ≤ r) (hr1 : r ≤ 1) (hw : 0 < w)
    (D : Set Λ) (J : Λ → ℝ) (Lf : ℤ → Finset ℤ) (Kf : ℕ) (hLf : ∀ σ, (Lf σ).card ≤ Kf)
    (hfine : ∀ l ∈ D, (l, t) ∈ E → ⌊J l / w⌋ ∈ Lf ⌊zS F (c l) t / q⌋)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJlip : ∀ l ∈ D, ∀ l' ∈ D, (l, t) ∈ E → (l', t) ∈ E → piece r l = piece r l' →
      |J l - J l'| ≤ CJ * r)
    (Kpop : ℝ) (hKpop : 0 < Kpop) :
    ∃ Lc : ℤ → Finset ℤ, (∀ τ, ((Lc τ).card : ℝ) ≤ 3 * K * Kf * Kpop) ∧
      ν {l | l ∈ D ∧ (l, t) ∈ E ∧ ⌊J l / w⌋ ∉ Lc ⌊zS F (c l) t / r⌋} ≤
        ENNReal.ofReal (4800 * K ^ 3 * (CJ * r / w + 1) / Kpop) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < q := lt_of_lt_of_le hSN.zeta_pos hζq
  have hr : 0 < r := lt_of_lt_of_le hq hqr
  have hζr : ζ ≤ r := hζq.trans hqr
  by_cases hex : ∃ l₀, (l₀, t) ∈ E
  swap
  · push Not at hex
    refine ⟨fun _ => ∅, fun τ => by simp; positivity, ?_⟩
    have : {l | l ∈ D ∧ (l, t) ∈ E ∧ ⌊J l / w⌋ ∉ (∅ : Finset ℤ)} = ∅ := by
      ext l; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h; exact absurd h (hex l)
    simp only at this ⊢
    rw [this, measure_empty]; exact bot_le
  obtain ⟨l₀, hl₀⟩ := hex
  have ht : t ∈ Icc (0 : ℝ) 1 := hSN.time_mem _ hl₀
  have hFt : ‖F t‖ ≤ K := hSN.row_le _ hl₀
  set θ : ℝ := (r / q) ^ d / Kpop with hθ
  have hθpos : 0 < θ := by positivity
  -- occupied fine bins in each coarse bin
  have hocc : ∀ τ : ℤ, ∃ B : Finset ℤ, (B.card : ℝ) ≤ 3 * (K * (r / q) ^ d) ∧
      ∀ l, (l, t) ∈ E → ⌊zS F (c l) t / r⌋ = τ → ⌊zS F (c l) t / q⌋ ∈ B := by
    intro τ
    obtain ⟨m, z, hcov, hm⟩ := hSN.support t q r (τ * r) hζq hqr
    have hS' : {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s ∧ ⌊s / r⌋ = τ} ⊆
        ⋃ j, Metric.closedBall (z j) q := by
      rintro s ⟨l, hl, rfl, hτ⟩
      apply hcov
      refine ⟨⟨l, hl, rfl⟩, ?_, ?_⟩
      · have := Int.floor_le (zS F (c l) t / r)
        rw [hτ] at this
        have := (le_div_iff₀ hr).mp this; linarith
      · have := Int.lt_floor_add_one (zS F (c l) t / r)
        rw [hτ] at this
        have := (div_lt_iff₀ hr).mp this; linarith
    obtain ⟨B, hB, hmem⟩ := card_floor_image_le hq hS'
    refine ⟨B, ?_, fun l hl hτ => hmem _ ⟨l, hl, rfl, hτ⟩⟩
    calc (B.card : ℝ) ≤ 3 * m := by exact_mod_cast hB
      _ ≤ 3 * (K * (r / q) ^ d) := by linarith
  choose Bτ hBτcard hBτmem using hocc
  -- counts and the popular lists
  let cnt : ℤ → ℤ → ℕ := fun τ v => ((Bτ τ).filter (fun σ => v ∈ Lf σ)).card
  let Lc : ℤ → Finset ℤ := fun τ => ((Bτ τ).biUnion Lf).filter (fun v => θ ≤ (cnt τ v : ℝ))
  refine ⟨Lc, ?_, ?_⟩
  · -- card bound by double counting
    intro τ
    have hdc : ∑ v ∈ Lc τ, (cnt τ v : ℝ) ≤ ∑ σ ∈ Bτ τ, ((Lf σ).card : ℝ) := by
      have : ∑ v ∈ Lc τ, cnt τ v ≤ ∑ σ ∈ Bτ τ, (Lf σ).card := by
        simp only [cnt, Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro σ _
        calc ∑ v ∈ Lc τ, (if v ∈ Lf σ then 1 else 0) = ((Lc τ).filter (· ∈ Lf σ)).card := by
              rw [Finset.card_filter]
          _ ≤ (Lf σ).card := Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
      exact_mod_cast this
    have hlow : (Lc τ).card * θ ≤ ∑ v ∈ Lc τ, (cnt τ v : ℝ) := by
      have := Finset.card_nsmul_le_sum (Lc τ) (fun v => (cnt τ v : ℝ)) θ
        (fun v hv => (Finset.mem_filter.mp hv).2)
      rwa [nsmul_eq_mul] at this
    have hup : ∑ σ ∈ Bτ τ, ((Lf σ).card : ℝ) ≤ (Bτ τ).card * Kf := by
      have := Finset.sum_le_card_nsmul (Bτ τ) (fun σ => ((Lf σ).card : ℝ)) (Kf : ℝ)
        (fun σ _ => by exact_mod_cast hLf σ)
      rwa [nsmul_eq_mul] at this
    have hKf : (0 : ℝ) ≤ Kf := Nat.cast_nonneg _
    have h1 : (Lc τ).card * θ ≤ 3 * (K * (r / q) ^ d) * Kf :=
      hlow.trans (hdc.trans (hup.trans (by gcongr; exact hBτcard τ)))
    have hrq : 0 < (r / q) ^ d := by positivity
    rw [hθ] at h1
    have h2 : ((Lc τ).card : ℝ) * (r / q) ^ d ≤ 3 * K * Kf * Kpop * (r / q) ^ d := by
      have := mul_le_mul_of_nonneg_right h1 hKpop.le
      field_simp at this
      nlinarith
    exact le_of_mul_le_mul_right h2 hrq
  · -- the unpopular mass
    set Bad := {l | l ∈ D ∧ (l, t) ∈ E ∧ ⌊J l / w⌋ ∉ Lc ⌊zS F (c l) t / r⌋} with hBad
    set C : ℝ := 4800 * K ^ 3 * (CJ * r / w + 1) / Kpop with hC
    have hC0 : 0 ≤ C := by positivity
    -- per piece
    have hpiece : ∀ b : Fin 7 → ℤ, ν (Bad ∩ piece r ⁻¹' {b}) ≤
        ENNReal.ofReal C * ν (piece r ⁻¹' {b}) := by
      intro b
      by_cases hb : ∃ lb ∈ D, (lb, t) ∈ E ∧ piece r lb = b
      swap
      · push Not at hb
        have : Bad ∩ piece r ⁻¹' {b} = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          rintro l ⟨⟨hlD, hlt, _⟩, hpb⟩
          exact hb l hlD hlt hpb
        rw [this, measure_empty]; exact bot_le
      obtain ⟨lb, hlbD, hlbt, hlbb⟩ := hb
      set Sb := zS F (c lb) t
      set yb := zy (c lb) t
      set δS := (3 + 4 * K) * r
      set Tb := Finset.Icc ⌊(Sb - δS) / r⌋ ⌊(Sb + δS) / r⌋
      set Vb := Finset.Icc ⌊(J lb - CJ * r) / w⌋ ⌊(J lb + CJ * r) / w⌋
      let Q : ℤ → Set Λ := fun σ =>
        {l | piece r l = b ∧ (l, t) ∈ E ∧ zS F (c l) t ∈ Ico (σ * q) (σ * q + q) ∧
          ∀ i, |zy (c l) t i - yb i| ≤ 2 * r}
      have hsub : Bad ∩ piece r ⁻¹' {b} ⊆ ⋃ τ ∈ Tb, ⋃ v ∈ Vb,
          ⋃ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ), Q σ := by
        rintro l ⟨⟨hlD, hlt, hnot⟩, hpb⟩
        simp only [mem_preimage, mem_singleton_iff] at hpb
        have hdiam : ‖c l - c lb‖ ≤ r :=
          hSN.piece_diam r hζr hr1 l lb (by rw [hpb, hlbb])
        set τ := ⌊zS F (c l) t / r⌋
        set σ := ⌊zS F (c l) t / q⌋
        set v := ⌊J l / w⌋
        have hτ : τ ∈ Tb := floor_mem_Icc_of_abs_le hr (abs_zS_sub_le hdiam ht hFt)
        have hv : v ∈ Vb := floor_mem_Icc_of_abs_le hw
          (hJlip l hlD lb hlbD hlt hlbt (by rw [hpb, hlbb]))
        have hσ : σ ∈ Bτ τ := hBτmem τ l hlt rfl
        have hvσ : v ∈ Lf σ := hfine l hlD hlt
        have hcnt : (cnt τ v : ℝ) < θ := by
          by_contra hge
          push Not at hge
          apply hnot
          exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨σ, hσ, hvσ⟩, hge⟩
        simp only [mem_iUnion, exists_prop]
        refine ⟨τ, hτ, v, hv, σ, Finset.mem_filter.mpr ⟨hσ, hvσ, hcnt⟩, hpb, hlt, ⟨?_, ?_⟩,
          fun i => abs_zy_sub_le hdiam ht i⟩
        · have := Int.floor_le (zS F (c l) t / q)
          have := (le_div_iff₀ hq).mp this; linarith
        · have := Int.lt_floor_add_one (zS F (c l) t / q)
          have := (div_lt_iff₀ hq).mp this; linarith
      -- the mass of one `Q σ`
      set ny : ℕ := ⌊2 * (2 * r) / q⌋₊ + 1
      set nx : ℕ := ⌊4 * K + 1⌋₊ + 1
      let corner : (Fin 2 → Fin ny) → Fin 2 → ℝ := fun j i => yb i - 2 * r + (j i : ℕ) * q
      have hQ : ∀ σ : ℤ, ν (Q σ) ≤
          ENNReal.ofReal (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))) * ν (piece r ⁻¹' {b}) := by
        intro σ
        let Sq : (Fin 2 → Fin ny) → ℕ → Set Λ := fun j i =>
          {l | piece r l = b ∧ (l, t) ∈ E ∧
            InCube (c l) t (colA (σ * q) (F t) (corner j) q + i * q) (corner j) q}
        have hQsub : Q σ ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin 2 → Fin ny)),
            ⋃ i ∈ Finset.range nx, Sq j i := by
          rintro l ⟨hpb, hlt, ⟨hs1, hs2⟩, hy⟩
          obtain ⟨j, hj, hbox⟩ := box_cover hq hy
          let jj : Fin 2 → Fin ny := fun i => ⟨j i, hj i⟩
          have hbox' : ∀ i, zy (c l) t i ∈ Ico (corner jj i) (corner jj i + q) := hbox
          obtain ⟨i, hi, hx⟩ := col_cover (s₀ := σ * q) (x := zx (c l) t) (y := zy (c l) t)
            (b := corner jj) hq hFt (by simpa [zS] using hs1) (by simpa [zS] using hs2) hbox'
          simp only [mem_iUnion, exists_prop, Finset.mem_range, Finset.mem_univ, true_and]
          exact ⟨jj, i, hi, hpb, hlt, hx, hbox'⟩
        refine (measure_mono hQsub).trans ?_
        refine (measure_biUnion_finset_le _ _).trans ?_
        have hsq : ∀ j i, ν (Sq j i) ≤ ENNReal.ofReal (K * (q / r) ^ (2 + d)) *
            ν (piece r ⁻¹' {b}) := by
          intro j i
          exact hSN.bin_cap r hζr hr1 b t _ (corner j) q hζq hqr
        calc ∑ j ∈ (Finset.univ : Finset (Fin 2 → Fin ny)), ν (⋃ i ∈ Finset.range nx, Sq j i)
            ≤ ∑ _j ∈ (Finset.univ : Finset (Fin 2 → Fin ny)), ∑ _i ∈ Finset.range nx,
                ENNReal.ofReal (K * (q / r) ^ (2 + d)) * ν (piece r ⁻¹' {b}) :=
              Finset.sum_le_sum fun j _ =>
                (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => hsq j i)
          _ = ENNReal.ofReal (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))) * ν (piece r ⁻¹' {b}) := by
              simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_fun,
                Fintype.card_fin, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ny ^ 2 * nx),
                ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ny ^ 2)]
              rw [show ((ny : ℝ) ^ 2) = ((ny ^ 2 : ℕ) : ℝ) by push_cast; ring,
                ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
              push_cast
              ring
      -- sum over the cover
      refine (measure_mono hsub).trans ?_
      have hstep : ν (⋃ τ ∈ Tb, ⋃ v ∈ Vb,
          ⋃ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ), Q σ) ≤
          ∑ τ ∈ Tb, ∑ v ∈ Vb, ∑ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ),
            ENNReal.ofReal (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))) * ν (piece r ⁻¹' {b}) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
        exact hQ σ
      refine hstep.trans ?_
      -- each inner filter has fewer than θ elements
      have hfilt : ∀ τ v,
          (((Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ)).card : ℝ) ≤ θ := by
        intro τ v
        by_cases hlt : (cnt τ v : ℝ) < θ
        · have : (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ) =
              (Bτ τ).filter (fun σ => v ∈ Lf σ) := by
            ext σ; simp [hlt]
          rw [this]; exact hlt.le
        · have : (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ) = ∅ := by
            ext σ; simp [hlt]
          rw [this]; simp; exact hθpos.le
      have hTb : (Tb.card : ℝ) ≤ 2 * δS / r + 2 := card_Icc_floor_le hr (by positivity)
      have hVb : (Vb.card : ℝ) ≤ 2 * (CJ * r) / w + 2 := card_Icc_floor_le hw (by positivity)
      -- bound the ENNReal sum by a real one
      have hreal : ∀ τ ∈ Tb, ∀ v ∈ Vb,
          ∑ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ),
            ENNReal.ofReal (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))) * ν (piece r ⁻¹' {b}) ≤
          ENNReal.ofReal (θ * (ny ^ 2 * nx * (K * (q / r) ^ (2 + d)))) *
            ν (piece r ⁻¹' {b}) := by
        intro τ _ v _
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        exact hfilt τ v
      calc ∑ τ ∈ Tb, ∑ v ∈ Vb,
            ∑ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ),
              ENNReal.ofReal (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))) * ν (piece r ⁻¹' {b})
          ≤ ∑ τ ∈ Tb, ∑ v ∈ Vb,
              ENNReal.ofReal (θ * (ny ^ 2 * nx * (K * (q / r) ^ (2 + d)))) *
                ν (piece r ⁻¹' {b}) :=
            Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun v hv => hreal τ hτ v hv
        _ = ENNReal.ofReal (Tb.card * (Vb.card *
              (θ * (ny ^ 2 * nx * (K * (q / r) ^ (2 + d)))))) * ν (piece r ⁻¹' {b}) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            simp only [ENNReal.ofReal_natCast]
            ring
        _ ≤ ENNReal.ofReal C * ν (piece r ⁻¹' {b}) := by
            gcongr
            -- the real inequality
            have hny : (ny : ℝ) ≤ 2 * (2 * r) / q + 1 :=
              floor_add_one_le (by positivity)
            have hnx : (nx : ℝ) ≤ 4 * K + 2 := by
              have := floor_add_one_le (B := 4 * K + 1) (by positivity); linarith
            have hθe : θ * (q / r) ^ (2 + d) = (q / r) ^ 2 / Kpop := by
              have h1 : (q / r) ^ (2 + d) = (q / r) ^ 2 * (q / r) ^ d := by
                rw [Real.rpow_add (by positivity), Real.rpow_two]
              have h2 : (r / q) ^ d * (q / r) ^ d = 1 := by
                rw [← Real.mul_rpow (by positivity) (by positivity)]
                rw [show r / q * (q / r) = 1 by field_simp, Real.one_rpow]
              rw [hθ, h1, show (r / q) ^ d / Kpop * ((q / r) ^ 2 * (q / r) ^ d) =
                ((r / q) ^ d * (q / r) ^ d) * (q / r) ^ 2 / Kpop by ring, h2, one_mul]
            have hrows : (2 * (2 * r) / q + 1) * (q / r) ≤ 5 := by
              rw [add_mul, one_mul]
              have : 2 * (2 * r) / q * (q / r) = 4 := by field_simp; ring
              rw [this]
              have : q / r ≤ 1 := (div_le_one hr).mpr hqr
              linarith
            have hny2 : (ny : ℝ) ^ 2 * (q / r) ^ 2 ≤ 25 := by
              have h0 : 0 ≤ (ny : ℝ) * (q / r) := by positivity
              have h1 : (ny : ℝ) * (q / r) ≤ 5 :=
                (mul_le_mul_of_nonneg_right hny (by positivity)).trans hrows
              nlinarith
            have hδS : 2 * δS / r + 2 = 8 * K + 8 := by
              simp only [δS]; field_simp; ring
            have e1 : (Tb.card : ℝ) * (Vb.card * (θ * (ny ^ 2 * nx * (K * (q / r) ^ (2 + d))))) =
                Tb.card * Vb.card * nx * K * (ny ^ 2 * (θ * (q / r) ^ (2 + d))) := by ring
            rw [e1, hθe]
            have hny' : (ny : ℝ) ^ 2 * ((q / r) ^ 2 / Kpop) ≤ 25 / Kpop := by
              rw [mul_div_assoc', div_le_div_iff_of_pos_right hKpop]
              exact hny2
            calc (Tb.card : ℝ) * Vb.card * nx * K * (ny ^ 2 * ((q / r) ^ 2 / Kpop))
                ≤ (8 * K + 8) * (2 * (CJ * r) / w + 2) * (4 * K + 2) * K * (25 / Kpop) := by
                  rw [← hδS]; gcongr
              _ ≤ C := by
                  rw [hC]
                  have h1 : 8 * K + 8 ≤ 16 * K := by linarith
                  have h2 : 4 * K + 2 ≤ 6 * K := by linarith
                  have h3 : 2 * (CJ * r) / w + 2 = 2 * (CJ * r / w + 1) := by ring
                  rw [h3]
                  have hX : 0 ≤ CJ * r / w + 1 := by positivity
                  calc (8 * K + 8) * (2 * (CJ * r / w + 1)) * (4 * K + 2) * K * (25 / Kpop)
                      ≤ (16 * K) * (2 * (CJ * r / w + 1)) * (6 * K) * K * (25 / Kpop) := by
                        gcongr
                    _ = 4800 * K ^ 3 * (CJ * r / w + 1) / Kpop := by ring
    -- sum over pieces
    have hcov : Bad ⊆ ⋃ b : Fin 7 → ℤ, Bad ∩ piece r ⁻¹' {b} := by
      intro l hl; exact mem_iUnion.mpr ⟨piece r l, hl, rfl⟩
    have hdisj : Pairwise (Function.onFun Disjoint fun b : Fin 7 → ℤ => piece r ⁻¹' {b}) := by
      intro b b' hbb'
      exact Disjoint.preimage _ (disjoint_singleton.mpr hbb')
    have hmeas : ∀ b : Fin 7 → ℤ, MeasurableSet (piece r ⁻¹' {b}) :=
      fun b => hSN.measurable_piece r (measurableSet_singleton b)
    have hprob := hSN.prob
    calc ν Bad ≤ ∑' b : Fin 7 → ℤ, ν (Bad ∩ piece r ⁻¹' {b}) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ ≤ ∑' b : Fin 7 → ℤ, ENNReal.ofReal C * ν (piece r ⁻¹' {b}) := ENNReal.tsum_le_tsum hpiece
      _ = ENNReal.ofReal C * ν (⋃ b : Fin 7 → ℤ, piece r ⁻¹' {b}) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
      _ ≤ ENNReal.ofReal C * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal C := mul_one _

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
