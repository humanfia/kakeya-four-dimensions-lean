-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.SingleTube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Split
import Submission.WZ.Obl.wz_coarse_grains_assembly.Singleton

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- The proposed single-tube theorem, assembled at radius one in the
frozen grains predicate. This remains conditional on `TubeGrains`. -/
theorem single_tube_grains_at_one (hTG : TubeGrains) {ω ζ τ ε : ℝ}
    (hω : 0 < ω) (hζ : 0 < ζ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (n : ℕ) (x v : Fin n → V) (Z : Fin n → Set V) (S : Finset (Fin n)) (y w : V),
        S.Nonempty → ‖w‖ = 1 →
        (∀ i ∈ S, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T (1 / 2) y w ∧
          MeasurableSet (Z i) ∧ Z i ⊆ T δ (x i) (v i)) →
        (∀ i, i ∉ S → Z i = ∅) → X δ n x v →
        O (δ ^ η * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Z i) →
        (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ 1 →
          q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
            δ ^ (-η) * r ^ (ω * ζ / 100) * q n {i | p ∈ Z i}) →
        4 * δ ^ ε / δ ≤ (S.card : ℝ) ∧
        ∀ c : ℝ, δ ^ (1 - τ) ≤ c → c ≤ δ ^ ε * (1 / δ) / S.card → 16 * δ ≤ c →
          ∃ (Z' : Fin n → Set V) (g : ℝ), 0 < g ∧
            (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S → Z' i = ∅)) ∧
            O (δ ^ ε) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S, μ (Z' i) ∧
            Broad ω ζ δ ε 1 n 1 v S Z' (fun _ => 0) ∧
            H δ ε n x v S Z' 1 1 (fun _ => y) (fun _ => w) (fun _ => 0) (16*δ) c 0 g := by
  obtain ⟨η, d, hη, hd, hmain⟩ := hTG (ω * ζ / 100) τ ε (by positivity) hτ hε
    O rfl q rfl T rfl X rfl P rfl
  refine ⟨η, min d (1 / 100), hη, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδd n x v Z S y w hS hw hgeom hzero hX hmass hbr
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨hcount, hgrains⟩ := hmain δ 1 hδ (hδd.trans (min_le_left _ _)) hδ1 le_rfl
    n x v Z S y w hS hw hgeom hzero hX hmass (by simpa only [div_one] using hbr)
  refine ⟨by simpa only [one_div, div_eq_mul_inv, one_mul] using hcount, ?_⟩
  intro c hclo hchi hwidth
  obtain ⟨Z', m, L, z, e, G, hZ', hmass', hbr', hmult, hgeom', hdisj, hunion, hmassG, hcross⟩ :=
    hgrains c (by simpa only [div_one] using hclo) hchi
  have hZzero (i : Fin n) (hi : i ∉ S) : Z' i = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := (hZ' i).2 hp
    rw [hzero i hi] at h
    exact h
  have hScard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hc1 : c ≤ 1 := by
    have hu : δ ^ ε * (1 / δ) / S.card ≤ (1 / 4 : ℝ) := by
      rw [div_le_iff₀ hScard]
      linarith [hcount]
    exact hchi.trans (hu.trans (by norm_num))
  refine ⟨Z', max 1 L, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    (fun i => ⟨(hZ' i).1, (hZ' i).2, hZzero i⟩), hmass',
    broad_singleton_of_global hZzero hbr', ?_⟩
  exact singleton_grains_of_boxes hδ (by linarith) (by simpa only [one_mul] using hwidth)
    (by simp) hc1 hZzero hgeom' hdisj hunion hmassG hmult hcross

end WangZahlLot.Obl.wz_coarse_grains_assembly
