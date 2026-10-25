-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_family_improvement.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_family_improvement.Scalar
import Submission.WZ.Obl.wz_concentrated_family_improvement.FactorVolume
import Submission.WZ.Obl.wz_concentrated_convex_factorization
import Submission.WZ.Obl.wz_flat_factored_improvement
import Submission.WZ.Obl.wz_nonflat_factored_improvement
import Submission.WZ.Obl.wz_tube_packing_bound

noncomputable section

namespace WangZahlLot.Obl.wz_concentrated_family_improvement

/-- Combine the two shapes of the factorization, choosing the gain before the threshold. -/
theorem improvement : ∀ σ ω u : ℝ,
    0 < σ → σ ≤ 1/2 → 0 < ω → ω < u → D σ ω → E σ u →
    ∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∀ θ : ℝ, 0 < θ →
      J (fun ε A ν δ => ∀ m : ℝ, 1 ≤ m →
        ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
          H ν δ n x v Y (K δ m (δ ^ (-ν)) n x v
            ((∀ i, o (δ ^ ν * δ ^ 2) ≤ μ (Y i)) → N θ ζ δ n x v →
              R σ (u - α) ε A δ m n ≤ μ (⋃ i, Y i)))) := by
  intro σ ω u hσ hσtop hω hωu hD hE ζ hζ
  have hu : 0 < u := hω.trans hωu
  obtain ⟨β, hβ, αN, hαN, hnonflat⟩ :=
    WangZahlLot.wz_nonflat_factored_improvement σ ω u hσ hσtop hω hωu hD hE ζ hζ
  obtain ⟨αF, hαF, hflat⟩ :=
    WangZahlLot.wz_flat_factored_improvement σ u hσ hσtop hu hE β hβ
  let α := min (min αF αN) (u / 2)
  have hα : 0 < α := lt_min (lt_min hαF hαN) (half_pos hu)
  have hαF' : α ≤ αF := (min_le_left _ _).trans (min_le_left _ _)
  have hαN' : α ≤ αN := (min_le_left _ _).trans (min_le_right _ _)
  have hαu : α ≤ u / 2 := min_le_right _ _
  refine ⟨α, hα, ?_⟩
  intro θ hθ ε hε
  obtain ⟨AF, hAF, ηF, hηF, dF, hdF, hflat⟩ := hflat ε hε
  obtain ⟨AN, hAN, ηN, hηN, dN, hdN, hnonflat⟩ := hnonflat ε hε
  let ν := min (min ηF ηN) (min θ (ζ / 2))
  have hν : 0 < ν := lt_min (lt_min hηF hηN) (lt_min hθ (half_pos hζ))
  have hνF : ν ≤ ηF := (min_le_left _ _).trans (min_le_left _ _)
  have hνN : ν ≤ ηN := (min_le_left _ _).trans (min_le_right _ _)
  have hνθ : ν ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hνζ : ν ≤ ζ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C, hC, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  obtain ⟨dX, hdX, hextract⟩ :=
    WangZahlLot.wz_concentrated_convex_factorization C ν hC hν
  let d := min (min dF dN) dX
  have hd : 0 < d := lt_min (lt_min hdF hdN) hdX
  have hdF' : d ≤ dF := (min_le_left _ _).trans (min_le_left _ _)
  have hdN' : d ≤ dN := (min_le_left _ _).trans (min_le_right _ _)
  have hdX' : d ≤ dX := min_le_right _ _
  obtain ⟨AC, hAC, hcompact⟩ := compact_coefficient
    (w := u - α) (ε := ε) (ν := ν) hσ.le hσtop (by linarith) hν.le hC hd
  let A := min (min AF AN) AC
  have hA : 0 < A := lt_min (lt_min hAF hAN) hAC
  have hAAF : A ≤ AF := (min_le_left _ _).trans (min_le_left _ _)
  have hAAN : A ≤ AN := (min_le_left _ _).trans (min_le_right _ _)
  have hAAC : A ≤ AC := min_le_right _ _
  refine ⟨A, hA, ν, hν, ?_⟩
  intro δ hδ hδ100 m hm n x v Y hn hv hT hover hY hYT hsum hKT hslab hind hno
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hcount : (n : ℝ) * δ ^ 4 ≤ C := hpack δ hδ hδ100 n x v hv hT hover
  by_cases hδd : δ ≤ d
  · obtain ⟨a, b, hδa, hab, hb, hfac⟩ :=
      hextract δ hδ hδ100 (hδd.trans hdX') m hm n x v hn hv hT hover hcount hKT
    have hvol := factorization_volume_bound hδ hδ1 hνθ hνζ hfac hno
    by_cases habflat : a ≤ δ ^ β * b
    · have hbnd := hflat ν hν hνF δ hδ hδ100 (hδd.trans hdF') m hm n x v Y
        hn hv hT hover hY hYT hsum hKT hslab hind a b hδa hab hb hfac habflat
      exact (target_mono hδ hδ1 hm0 hA.le hAAF (by linarith : u - αF ≤ u - α)).trans hbnd
    · have hbnd := hnonflat ν hν hνN δ hδ hδ100 (hδd.trans hdN') m hm n x v Y
        hn hv hT hover hY hYT hsum hKT hslab hind a b hδa hab hb hfac hvol
        (lt_of_not_ge habflat)
      exact (target_mono hδ hδ1 hm0 hA.le hAAN (by linarith : u - αN ≤ u - α)).trans hbnd
  · have hsmall := hcompact δ hδ (le_of_not_ge hδd) hδ1 m hm n hn hcount
    have hsingle : o (δ ^ ν * δ ^ 2) ≤ μ (⋃ i, Y i) :=
      (hind ⟨0, hn⟩).trans (MeasureTheory.measure_mono (Set.subset_iUnion Y ⟨0, hn⟩))
    exact (target_mono hδ hδ1 hm0 hA.le hAAC le_rfl).trans (hsmall.trans hsingle)

end WangZahlLot.Obl.wz_concentrated_family_improvement
