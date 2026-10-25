-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_alternative_remove_cutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_grains_alternative_remove_cutoff`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_grains_alternative_remove_cutoff`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_grains_alternative_remove_cutoff/`
belong to this obligation.
-/

namespace WangZahlLot.Obl.wz_grains_alternative_remove_cutoff

/-- Real-arithmetic core of the large-scale case of the cutoff removal: when `d₀ < δ ≤ 1`,
`n ≥ 1` and `n δ² ≤ δ^(-η) C` (the convex count applied to the unit ball, of volume `C`),
the gain expression is dominated by the trivial lower bound `δ^η δ²` on the volume of the
union, as soon as `κ (C + 1) ≤ d₀^5`. -/
theorem gain_le_trivial {σ ω α η κ δ d₀ C : ℝ} {n : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hαω : α ≤ ω) (hη1 : η ≤ 1)
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hκC : κ * (C + 1) ≤ d₀ ^ 5) (hd₀ : 0 < d₀)
    (hδ : d₀ < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ (n : ℝ))
    (hK : (n : ℝ) * δ ^ 2 ≤ δ ^ (-η) * C) :
    κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ) ≤ δ ^ η * δ ^ 2 := by
  have hδ0 : 0 < δ := hd₀.trans hδ
  have hδne : δ ≠ 0 := hδ0.ne'
  have ha : δ ^ (ω - α) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 (sub_nonneg.mpr hαω)
  have hb : ((n : ℝ) * δ) ^ (-σ) ≤ δ⁻¹ :=
    calc ((n : ℝ) * δ) ^ (-σ) ≤ δ ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hδ0 (le_mul_of_one_le_left hδ0.le hn) (by linarith)
      _ ≤ δ ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ = δ⁻¹ := Real.rpow_neg_one δ
  have hc : (n : ℝ) * δ ^ 2 ≤ δ⁻¹ * C :=
    calc (n : ℝ) * δ ^ 2 ≤ δ ^ (-η) * C := hK
      _ ≤ δ ^ (-1 : ℝ) * C :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)) hC
      _ = δ⁻¹ * C := by rw [Real.rpow_neg_one]
  have hd : δ ≤ δ ^ η :=
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hη1
  have h5 : κ * C ≤ δ ^ 5 :=
    calc κ * C ≤ κ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hκ
      _ ≤ d₀ ^ 5 := hκC
      _ ≤ δ ^ 5 := pow_le_pow_left₀ hd₀.le hδ.le 5
  have hnd : 0 ≤ (n : ℝ) * δ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ)
  have hκ1 : 0 ≤ κ * 1 := by simpa using hκ
  have hstep : κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ) ≤ κ * 1 * (δ⁻¹ * C) * δ⁻¹ := by
    have h1 : κ * δ ^ (ω - α) ≤ κ * 1 := mul_le_mul_of_nonneg_left ha hκ
    have h2 : κ * δ ^ (ω - α) * (n * δ ^ 2) ≤ κ * 1 * (δ⁻¹ * C) :=
      mul_le_mul h1 hc hnd hκ1
    exact mul_le_mul h2 hb (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ0.le) _)
      (mul_nonneg hκ1 (mul_nonneg (inv_nonneg.mpr hδ0.le) hC))
  have hmid : κ * 1 * (δ⁻¹ * C) * δ⁻¹ * δ ^ 2 = κ * C := by
    field_simp
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ0 2
  have hlast : κ * 1 * (δ⁻¹ * C) * δ⁻¹ ≤ δ ^ 3 := by
    refine le_of_mul_le_mul_right ?_ hδ2
    rw [hmid]
    calc κ * C ≤ δ ^ 5 := h5
      _ = δ ^ 3 * δ ^ 2 := by ring
  calc κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)
      ≤ κ * 1 * (δ⁻¹ * C) * δ⁻¹ := hstep
    _ ≤ δ ^ 3 := hlast
    _ = δ * δ ^ 2 := by ring
    _ ≤ δ ^ η * δ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg δ)

end WangZahlLot.Obl.wz_grains_alternative_remove_cutoff

theorem WangZahlLot.wz_grains_alternative_remove_cutoff : ∀σ ω:ℝ,0<σ→σ≤1/2→0<ω→ω≤1→(fun(V:Type) [NormedAddCommGroup V][InnerProductSpace ℝ V](μ:Set V→ENNReal)(ι:V→Fin 3→ℝ)(M:Set V→Prop)=>∀O,O=ENNReal.ofReal→∀q,q=(fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))→∀I,I=Metric.ball (0:V) 1→∀T,T=(fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))→∀Q,Q=(fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})→∀X,X=(fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))→∀K,K=(fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)→∀F,F=(fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))→∀A,A=(fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)→∀U:(δ:ℝ)→(n:ℕ)→(Fin n→V)→(Fin n→V)→(Fin n→Set V)→Prop,∀h:ℝ,0<h→(∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨U δ n x v Y)→∃α:ℝ,0<α∧∃κ:ℝ,0<κ∧∃η:ℝ,0<η∧η≤h∧∀δ:ℝ,0<δ→δ≤1/100→∀n x v Y,A δ η (δ^(-η)) (δ^(-η)) n x v Y→O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨U δ n x v Y) LeanEval.Analysis.WangZahlKakeya.Space MeasureTheory.volume (fun p i=>p i) MeasurableSet := by
  intro σ ω hσ hσ1 hω hω1
  rintro O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl U h hh hyp
  obtain ⟨α, κ, η, d₀, hα, hκ, hη, hd₀, hd₀1, H⟩ := hyp
  -- the volume of the unit ball, a finite constant
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧
      MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) =
        ENNReal.ofReal C :=
    ⟨_, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal MeasureTheory.measure_ball_lt_top.ne).symm⟩
  -- the new parameters
  obtain ⟨η', hη'0, hη'η, hη'h, hη'1⟩ : ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧ η' ≤ h ∧ η' ≤ 1 :=
    ⟨min (min η h) 1, lt_min (lt_min hη hh) one_pos, (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨α', hα'0, hα'α, hα'ω⟩ : ∃ α' : ℝ, 0 < α' ∧ α' ≤ α ∧ α' ≤ ω :=
    ⟨min α ω, lt_min hα hω, min_le_left _ _, min_le_right _ _⟩
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  obtain ⟨κ', hκ'0, hκ'κ, hκ'C⟩ : ∃ κ' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ κ' * (C + 1) ≤ d₀ ^ 5 := by
    refine ⟨min κ (d₀ ^ 5 / (C + 1)), lt_min hκ (div_pos (pow_pos hd₀ 5) hC1),
      min_le_left _ _, ?_⟩
    calc min κ (d₀ ^ 5 / (C + 1)) * (C + 1) ≤ d₀ ^ 5 / (C + 1) * (C + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hC1.le
      _ = d₀ ^ 5 := div_mul_cancel₀ _ hC1.ne'
  refine ⟨α', hα'0, κ', hκ'0, η', hη'0, hη'h, ?_⟩
  intro δ hδ hδ1 n x v Y hA
  have hδ1' : δ ≤ 1 := hδ1.trans (by norm_num)
  try dsimp only at hA
  obtain ⟨hn, hgeom, hX, hdens, hK, hF⟩ := hA
  by_cases hsmall : δ ≤ d₀
  · -- small scales: the supplied alternative, after raising the admissibility exponent
    have hpow : δ ^ (-η') ≤ δ ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (neg_le_neg hη'η)
    rcases H δ hδ hsmall n x v Y ⟨hn, hgeom, hX,
        hdens.trans' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' hη'η)
            (Nat.cast_nonneg n)) (sq_nonneg δ))),
        fun W hW => (hK W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl),
        fun u t r hu hr => (hF u t r hu hr).trans (mul_le_mul'
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg n)))
          le_rfl)⟩
      with hgain | hU
    · left
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hgain
      refine mul_le_mul_of_nonneg_right ?_
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ.le) _)
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ))
      exact mul_le_mul hκ'κ (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith))
        (Real.rpow_nonneg hδ.le _) hκ.le
    · exact Or.inr hU
  · -- large scales: the gain follows from the density lower bound and the convex count
    -- on the unit ball
    left
    have hd₀δ : d₀ < δ := not_le.mp hsmall
    have hset : {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1} = Set.univ :=
      Set.eq_univ_of_forall (fun i => (hgeom i).2.1)
    have hKI : ENNReal.ofReal (({i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η')) *
          MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) :=
      hK _ (convex_ball _ _)
    rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hCeq,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)] at hKI
    have hKr : (n : ℝ) * δ ^ 2 ≤ δ ^ (-η') * C :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hδ.le _) hC0)).mp hKI
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    have hreal := WangZahlLot.Obl.wz_grains_alternative_remove_cutoff.gain_le_trivial
      hσ (by linarith) hα'ω hη'1 hκ'0.le hC0 hκ'C hd₀ hd₀δ hδ1' hn1 hKr
    have hsum : ∑ i, MeasureTheory.volume (Y i) ≤ n * MeasureTheory.volume (⋃ i, Y i) := by
      calc ∑ i, MeasureTheory.volume (Y i) ≤ ∑ _i : Fin n, MeasureTheory.volume (⋃ j, Y j) :=
            Finset.sum_le_sum (fun i _ => MeasureTheory.measure_mono (Set.subset_iUnion Y i))
        _ = n * MeasureTheory.volume (⋃ i, Y i) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← ENNReal.mul_le_mul_iff_right hn0 (ENNReal.natCast_ne_top n)]
    calc (n : ENNReal) * ENNReal.ofReal (κ' * δ ^ (ω - α') * (n * δ ^ 2) * (n * δ) ^ (-σ))
        ≤ n * ENNReal.ofReal (δ ^ η' * δ ^ 2) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hreal)
      _ = ENNReal.ofReal (δ ^ η' * n * δ ^ 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring
      _ ≤ ∑ i, MeasureTheory.volume (Y i) := hdens
      _ ≤ n * MeasureTheory.volume (⋃ i, Y i) := hsum
