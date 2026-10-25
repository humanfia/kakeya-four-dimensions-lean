import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodDataOfAE
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeParentLists

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set

noncomputable section

namespace Parent.NativeParentLists

variable {α : Type} [MeasurableSpace α] {p : Parent α}
    {k : ℕ} {r m H H₀ R : ℝ} {L : ProjectedLayer α} {σ : Measure (α × ℝ)}
    (n : p.NativeParentLists k r m H L σ)

def forwardByCode (Q : Fin (p.n k r)) (c : (Fin 2 → ℤ) × (ℤ × ℤ × ℤ)) :
    Finset (Fin L.count) := n.coarseChoices Q c.1

def reverseByCode (i : Fin L.count) (c : (Fin 2 → ℤ) × (ℤ × ℤ × ℤ)) :
    Finset (Fin (p.n k r)) := n.reverseChoices c.1 c.2 i

/-- Away from null block endpoints, the original native selectors equal
every true/projected label occurring at that incidence. Thus the native
lists hold for the literal labels used by the final table. -/
theorem ae_all_choices (hbase : p.Basic) (hσ : σ ≤ p.μ k)
    (hat : p.AtDepth k r R) (hL : L.Valid p k r m H₀) :
    ∀ᵐ ω ∂n.law, p.NativeChoicesAt k r m L n.forwardByCode n.reverseByCode ω := by
  have ht := (Parent.Basic.ae_short_time_code p hbase k r m).filter_mono
    (ae_mono (n.le_source.trans hσ))
  filter_upwards [n.source_data, ht] with ω hn htime
  obtain ⟨hB, hT, hC, hF, hR⟩ := hn
  intro Q i hQ hQt hi
  have hj : p.j k r Q = p.j k r (n.parent ω) := by
    apply Fin.ext
    exact_mod_cast (htime Q hQt).symm.trans (htime (n.parent ω) hT)
  have hQeq : Q = n.parent ω := by
    by_contra hne
    exact Set.disjoint_left.mp (hat.2.2.2.1 Q (n.parent ω) hne hj)
      ((hat.2.2.1 Q).2.2 hQ) ((hat.2.2.1 (n.parent ω)).2.2 hB)
  have hieq : i = n.coarse ω := by
    by_contra hne
    exact Set.disjoint_left.mp (hL.2.2.2.2.1 i (n.coarse ω) hne) hi hC
  have hbins := (hL.2.2.2.2.2.1 (n.coarse ω)).2.2.2.1 ω.1 hC
  have htag : (p.shortComparisonCode k r m ω).1 = L.tag (n.coarse ω) := by
    ext a
    fin_cases a
    · exact hbins.1
    · exact hbins.2.1
  rw [hQeq, hieq]
  change n.coarse ω ∈ n.coarseChoices (n.parent ω) (p.shortComparisonCode k r m ω).1 ∧
    n.parent ω ∈ n.reverseChoices (p.shortComparisonCode k r m ω).1
      (p.shortComparisonCode k r m ω).2 (n.coarse ω)
  rw [htag]
  exact ⟨hF, hR⟩

end Parent.NativeParentLists
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
