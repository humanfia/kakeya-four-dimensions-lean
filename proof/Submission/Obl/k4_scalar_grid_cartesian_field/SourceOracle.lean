import Submission.Obl.k4_scalar_grid_cartesian_field.SourcePacket
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreScales

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The frozen qualification oracle and original caps supply actual qualified nonsteep packets.
All selected mass floors retain the full original trajectory assignment. -/
theorem exists_source_packets (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (hpacket : packetHyp data)
    (E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence) (hqual : qualOracle data E₀) :
    ∃ (M : ℕ) (H : ℕ → ℝ) (B : ℝ)
      (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
      (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (ε L : ℕ → ℝ),
      2 ≤ M ∧ 2 ≤ data.κ * (M : ℝ) ∧ 50 ≤ B ∧ graphData data E₀ 40 H B G E ∧
      (∀ k, 0 < ε k) ∧ subpower data (fun k => data.N k ^ ε k) ∧ subpower data L ∧
      (∀ k, 2 * data.K k ≤ L k ∧ 3000 * data.K k ^ 3 ≤ L k) ∧
      ∀ᶠ k in atTop, Nonempty (SourcePacket data k M G E B (ε k) (L k) (H k)) := by
  obtain ⟨M, hM, hκM⟩ := exists_qualification_degree hs.2.2.2.2.2.1
  obtain ⟨H, B, G, E, hgraph, hfit⟩ := hqual M hM 40 (by norm_num)
  obtain ⟨ε, hε, _, hεsub, hqualified⟩ := qualified_parts_slow_accuracy data hs hb M 40 B H G E E₀
    hgraph (by simpa only [unqualified] using hfit)
  obtain ⟨Q, L, _, hLsub, hLb, hnonsteep⟩ := exists_nonsteep_selection data hs hb hcap hpacket H hgraph.1
  refine ⟨M, H, B, G, E, ε, L, hM, hκM, ?_, hgraph, hε, hεsub, hLsub, hLb, ?_⟩
  · simpa only [show (40 : ℝ) + 10 = 50 by norm_num] using hgraph.2.1
  · filter_upwards [hqualified, hnonsteep, original_packet_facts_eventually data hs hb hpacket,
      hpacket 2 (by norm_num)] with k hq hn hp hpk
    have hclean := clean_parts_of_qualified hb G E H (hgraph.1.1 k) hq hn.1 hn.2.1
    obtain ⟨_, _, _, hdisj, _, hcover⟩ := hpk 1 (by norm_num) (by norm_num)
    exact source_packet_of_clean hb G E H (hgraph.1.1 k) hclean hp hcover hdisj hn.2.2

end Submission.Obl.k4_scalar_grid_cartesian_field
