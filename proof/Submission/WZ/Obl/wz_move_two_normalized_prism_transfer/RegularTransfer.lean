-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.RegularTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.RegularRestriction
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Balance
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.StageTwo
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.RegularBudgets
import Submission.WZ.Obl.wz_coarse_grains_assembly.FibreSize

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- Once avoidance and a common multiplicity interval have been established,
whole-fibre balancing gives every clause of the frozen transfer output. -/
theorem balance_and_assemble_regular_prisms {ω ζ δ η h t ε ρ c m R : ℝ} {n b : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) (hηt : η ≤ t)
    (hhε : h ≤ ε) (htε : t ≤ ε)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (D : PrismData ω ζ δ h ρ c n x v Y)
    {S : Finset (Fin n)} {f : Fin n → Fin D.N}
    (hassign : ∀ i j, (D.W i j).Nonempty → i ∈ S ∧ f i = D.γ j)
    (hcont : ∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (D.y (f i)) (D.w (f i)))
    (huniq : ∀ i ∈ S, ∀ k k', T δ (x i) (v i) ⊆ T ρ (D.y k) (D.w k) →
      T δ (x i) (v i) ⊆ T ρ (D.y k') (D.w k') → k = k')
    (hmult : ∀ j p, p ∈ pieceSupport D.W j →
      q n {i | p ∈ D.W i j} ∈ Set.Icc m (2 * m))
    (havoid : ∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
      Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j)))
    (hb : 0 < b) (hR : 1 < R) (hbn : (n : ℝ) < R ^ b)
    (hmassbudget : (b : ℝ) * δ ^ t ≤ δ ^ h)
    (hFbudget : R * (56 * δ ^ (-(4 * t))) * δ ^ (-η) ≤ δ ^ (-ε))
    (hRbudget : R ≤ δ ^ (-ε)) (hone : 1 ≤ δ ^ (-ε)) :
    ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ)
      (y' w' : Fin N' → V) (f' : Fin n → Fin N') (g : ℝ),
      C δ ε n x v Y S' Z' ρ N' y' w' f' True ∧ 0 < g ∧
      Broad ω ζ δ ε ρ n N' v S' Z' f' ∧ H δ ε n x v S' Z' ρ N' y' w' f' D.a c 0 g := by
  classical
  have hZ : ∀ i, MeasurableSet (pieceUnion D.W i) ∧ pieceUnion D.W i ⊆ Y i ∧
      (i ∉ S → pieceUnion D.W i = ∅) := by
    intro i
    refine ⟨MeasurableSet.iUnion (fun j => (D.pieces i j).1), ?_, ?_⟩
    · intro p hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      exact ((D.pieces i j).2.1 hpj).1
    · intro hi
      apply Set.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      exact hi (hassign i j ⟨p, hpj⟩).1
  have hmass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (pieceUnion D.W i) := by
    calc
      _ ≤ ∑ i, ∑ j, μ (D.W i j) := D.mass
      _ = ∑ i, μ (pieceUnion D.W i) :=
        (pieceUnion_mass D.W (fun i j => (D.pieces i j).1)
          (fun i j j' hne => (D.pieces i j).2.2 j' hne)).symm
      _ = _ := (Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by simp only [(hZ i).2.2 hi, μ, measure_empty])).symm
  obtain ⟨Q, hQ, hC, hbr, _⟩ := balance_assigned_cover hδ hδ1 ht hηt hhε htε
    hA hZ hmass D.unit hcont D.distinct huniq
    (pieceUnion_broad hassign D.disjoint D.broad)
    hb hR hbn hmassbudget hFbudget hRbudget hone
  obtain ⟨g, hg, hH⟩ := grains_on_selected_fibres hδ D hassign hmult havoid Q hQ
  exact ⟨_, _, _, _, _, _, g, hC, hg, hbr,
    WangZahlLot.Obl.wz_coarse_grains_assembly.H_mono hδ hδ1 hhε hH⟩

/-- The full progress alternative, at unchanged scales, for prism data satisfying
the two extra regularity conditions. The input error and cutoff are uniform over
all geometric scales and all finite families. -/
theorem regular_prism_transfer {ω ζ ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
          A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
          ∀ (ρ c : ℝ) (D : PrismData ω ζ δ η ρ c n x v Y) (m : ℝ),
            (∀ j p, p ∈ pieceSupport D.W j →
              q n {i | p ∈ D.W i j} ∈ Set.Icc m (2 * m)) →
            (∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
              Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j))) →
            ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ)
              (y w : Fin N → V) (f : Fin n → Fin N) (g : ℝ),
              C δ ε n x v Y S Z ρ N y w f True ∧ 0 < g ∧
              Broad ω ζ δ ε ρ n N v S Z f ∧ H δ ε n x v S Z ρ N y w f D.a c 0 g := by
  let s := min (ε / 100) 1
  have hs : 0 < s := lt_min (by positivity) zero_lt_one
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsε : 100 * s ≤ ε := by
    have hh : s ≤ ε / 100 := min_le_left _ _
    linarith
  obtain ⟨b, d₀, hb, hd₀, hd₀1, hbudget⟩ := regular_prism_budgets hs hs1
  refine ⟨s, d₀, hs, by linarith, hd₀, ?_⟩
  intro δ hδ hδ0 n x v Y hA ρ c D m hmult havoid
  have hδ1 : δ ≤ 1 := hδ0.trans hd₀1.le
  obtain ⟨haB, hcountB, hR, hnB, hmB, hFB, hRB, h1B⟩ := hbudget δ hδ hδ0
  obtain ⟨D', f, S, Z, ha, hZ, hmass, hcont, hassign, hZeq, hbr, huniq,
      fj, hfj, hW, hbox, hγ⟩ :=
    assigned_stage_two_with_embedding hδ hδ1 (by linarith : s ≤ 2 * s) hA D haB
  have hmult' : ∀ j p, p ∈ pieceSupport D'.W j →
      q n {i | p ∈ D'.W i j} ∈ Set.Icc m (2 * m) := by
    intro j p hp
    have hp' : p ∈ pieceSupport D.W (fj j) := by
      simpa only [pieceSupport, hW] using hp
    simpa only [hW] using hmult (fj j) p hp'
  have havoid' : ∀ i j j', j ≠ j' → D'.γ j = D'.γ j' → (D'.W i j).Nonempty →
      Disjoint (D'.W i j') (P D'.a (ρ * c) c (D'.z j) (D'.e j)) := by
    intro i j j' hne he hnonempty
    rw [hW, hbox]
    exact havoid i (fj j) (fj j') (fun hh => hne (hfj hh)) (hγ j j' he)
      (by simpa only [hW] using hnonempty)
  have hn : (n : ℝ) < (δ ^ (-s)) ^ b :=
    (WangZahlLot.Obl.wz_coarse_grains_assembly.fine_count_power_seven hδ hcountB
      (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.1) hA.2.2.1).trans_lt hnB
  obtain ⟨S', Z', N', y', w', f', g, hC', hg, hbr', hH'⟩ :=
    balance_and_assemble_regular_prisms hδ hδ1 (by positivity : 0 ≤ 4 * s)
      (by linarith : s ≤ 4 * s) (by linarith : 2 * s ≤ 100 * s)
      (by linarith : 4 * s ≤ 100 * s) hA D' hassign hcont
      (fun i _ => huniq i) hmult' havoid' hb hR hn hmB hFB hRB h1B
  refine ⟨S', Z', N', y', w', f', g,
    WangZahlLot.Obl.wz_coarse_grains_assembly.C_mono hδ hδ1 hsε hC', hg,
    WangZahlLot.Obl.wz_coarse_grains_assembly.Broad_mono hδ hδ1 hsε hbr', ?_⟩
  simpa only [ha] using WangZahlLot.Obl.wz_coarse_grains_assembly.H_mono hδ hδ1 hsε hH'

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
