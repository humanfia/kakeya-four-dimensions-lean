import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Parallelogram

/-!
# Coarsening a list (deterministic replacement of `a04:entropy-independence`)

Fix a time `t`.  Suppose a quantity `J` of the labelled trajectories of a set `D` is determined,
at width `w`, by the fine scalar bin `⌊S/q⌋` up to `Kf` values, and is `CJ r`-Lipschitz inside a
coefficient piece of scale `r ≥ q`.  Then outside a set of prior mass
`≤ 480 K³ (CJ r / w + 1) / Kpop`, it is determined by the *coarse* scalar bin `⌊S/r⌋` up to
`3 K Kf Kpop` values: keep, in each coarse bin, the values listed by at least
`(r/q)^d / Kpop` of its occupied fine bins.  A value listed by fewer fine bins can only be taken
by trajectories whose fine scalar bins are few among the `≈ (r/q)^d` fine bins that the
conditional cap `BC` spreads every coefficient piece over.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

theorem abs_zy_sub_le {c c' : Fin 5 → ℝ} {r t : ℝ} (h : ‖c - c'‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zy c t - zy c' t| ≤ 2 * r := by
  have h3 : |c 3 - c' 3| ≤ r := by
    have := norm_le_pi_norm (c - c') 3; rw [Real.norm_eq_abs] at this; simpa using this.trans h
  have h4 : |c 4 - c' 4| ≤ r := by
    have := norm_le_pi_norm (c - c') 4; rw [Real.norm_eq_abs] at this; simpa using this.trans h
  unfold zy
  have : c 3 + c 4 * t - (c' 3 + c' 4 * t) = (c 3 - c' 3) + (c 4 - c' 4) * t := by ring
  rw [this]
  calc |(c 3 - c' 3) + (c 4 - c' 4) * t| ≤ |c 3 - c' 3| + |(c 4 - c' 4) * t| := abs_add_le _ _
    _ = |c 3 - c' 3| + |c 4 - c' 4| * t := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ r + r * 1 := by
        have := mul_le_mul h4 ht.2 ht.1 (le_trans (abs_nonneg _) h4)
        linarith
    _ = 2 * r := by ring

theorem abs_zx_sub_le {c c' : Fin 5 → ℝ} {r t : ℝ} (h : ‖c - c'‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zx c t - zx c' t| ≤ 3 * r := by
  have hc : ∀ e, |c e - c' e| ≤ r := fun e => by
    have := norm_le_pi_norm (c - c') e; rw [Real.norm_eq_abs] at this; simpa using this.trans h
  have := abs_zx_le (c := c - c') (K := r) (fun e => by simpa using hc e) ht
  have e : zx (c - c') t = zx c t - zx c' t := by simp only [zx, Pi.sub_apply]; ring
  rwa [e] at this

theorem abs_zS_sub_le {F : ℝ → ℝ} {c c' : Fin 5 → ℝ} {r t K : ℝ} (h : ‖c - c'‖ ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hF : |F t| ≤ K) : |zS F c t - zS F c' t| ≤ (3 + 2 * K) * r := by
  have hx := abs_zx_sub_le h ht
  have hy := abs_zy_sub_le h ht
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hF
  have e : zS F c t - zS F c' t = (zx c t - zx c' t) - F t * (zy c t - zy c' t) := by
    simp only [zS]; ring
  rw [e]
  calc |(zx c t - zx c' t) - F t * (zy c t - zy c' t)|
      ≤ |zx c t - zx c' t| + |F t| * |zy c t - zy c' t| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 3 * r + K * (2 * r) := by gcongr
    _ = (3 + 2 * K) * r := by ring

/-- Values of `⌊y / w⌋` for `y` within `δ` of `y₀`. -/
theorem floor_mem_Icc_of_abs_le {y y₀ δ w : ℝ} (hw : 0 < w) (h : |y - y₀| ≤ δ) :
    ⌊y / w⌋ ∈ Finset.Icc ⌊(y₀ - δ) / w⌋ ⌊(y₀ + δ) / w⌋ := by
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)

theorem card_Icc_floor_le {y₀ δ w : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) :
    ((Finset.Icc ⌊(y₀ - δ) / w⌋ ⌊(y₀ + δ) / w⌋).card : ℝ) ≤ 2 * δ / w + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le ((y₀ + δ) / w)
  have h2 := Int.lt_floor_add_one ((y₀ - δ) / w)
  have h3 : (y₀ + δ) / w - (y₀ - δ) / w = 2 * δ / w := by field_simp; ring
  have hle : (0 : ℤ) ≤ ⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋ := by
    have : ⌊(y₀ - δ) / w⌋ ≤ ⌊(y₀ + δ) / w⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)
    omega
  have hcast : (((⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋).toNat : ℕ) : ℝ) =
      ((⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hle
  rw [hcast]
  push_cast
  linarith

/-- **Coarsening a fine list.** -/
theorem coarsen_lists {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 5 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ}
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
        ENNReal.ofReal (480 * K ^ 3 * (CJ * r / w + 1) / Kpop) := by
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
  have hFt : |F t| ≤ K := hSN.row_le _ hl₀
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
    set C : ℝ := 480 * K ^ 3 * (CJ * r / w + 1) / Kpop with hC
    have hC0 : 0 ≤ C := by positivity
    -- per piece
    have hpiece : ∀ b : Fin 5 → ℤ, ν (Bad ∩ piece r ⁻¹' {b}) ≤
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
      set δS := (3 + 2 * K) * r
      set Tb := Finset.Icc ⌊(Sb - δS) / r⌋ ⌊(Sb + δS) / r⌋
      set Vb := Finset.Icc ⌊(J lb - CJ * r) / w⌋ ⌊(J lb + CJ * r) / w⌋
      let Q : ℤ → Set Λ := fun σ =>
        {l | piece r l = b ∧ (l, t) ∈ E ∧ zS F (c l) t ∈ Ico (σ * q) (σ * q + q) ∧
          |zy (c l) t - yb| ≤ 2 * r}
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
        refine ⟨τ, hτ, v, hv, σ, Finset.mem_filter.mpr ⟨hσ, hvσ, hcnt⟩, hpb, hlt, ⟨?_, ?_⟩, ?_⟩
        · have := Int.floor_le (zS F (c l) t / q)
          have := (le_div_iff₀ hq).mp this; linarith
        · have := Int.lt_floor_add_one (zS F (c l) t / q)
          have := (div_lt_iff₀ hq).mp this; linarith
        · exact abs_zy_sub_le hdiam ht
      -- the mass of one `Q σ`
      set ny : ℕ := ⌊2 * (2 * r) / q⌋₊ + 1
      set nx : ℕ := ⌊2 * K⌋₊ + 2
      have hQ : ∀ σ : ℤ, ν (Q σ) ≤ ENNReal.ofReal (ny * nx * (K * (q / r) ^ (1 + d))) *
          ν (piece r ⁻¹' {b}) := by
        intro σ
        let Sq : ℕ → ℕ → Set Λ := fun j i =>
          {l | piece r l = b ∧ (l, t) ∈ E ∧
            zx (c l) t ∈ Ico (paraA (σ * q) (F t) yb (2 * r) q j + i * q)
              (paraA (σ * q) (F t) yb (2 * r) q j + i * q + q) ∧
            zy (c l) t ∈ Ico (paraB yb (2 * r) q j) (paraB yb (2 * r) q j + q)}
        have hQsub : Q σ ⊆ ⋃ j ∈ Finset.range ny, ⋃ i ∈ Finset.range nx, Sq j i := by
          rintro l ⟨hpb, hlt, ⟨hs1, hs2⟩, hy⟩
          have hs1' : σ * q ≤ zx (c l) t - F t * zy (c l) t := by simpa [zS] using hs1
          have hs2' : zx (c l) t - F t * zy (c l) t < σ * q + q := by simpa [zS] using hs2
          obtain ⟨j, hj, i, hi, hx, hy'⟩ := para_cover hq hFt hs1' hs2' hy
          simp only [mem_iUnion, exists_prop, Finset.mem_range]
          exact ⟨j, hj, i, hi, hpb, hlt, hx, hy'⟩
        refine (measure_mono hQsub).trans ?_
        refine (measure_biUnion_finset_le _ _).trans ?_
        have hsq : ∀ j i, ν (Sq j i) ≤ ENNReal.ofReal (K * (q / r) ^ (1 + d)) *
            ν (piece r ⁻¹' {b}) := by
          intro j i
          have := hSN.bin_cap r hζr hr1 b t (paraA (σ * q) (F t) yb (2 * r) q j + i * q)
            (paraB yb (2 * r) q j) q hζq hqr
          simpa [Sq, preimage, mem_singleton_iff] using this
        calc ∑ j ∈ Finset.range ny, ν (⋃ i ∈ Finset.range nx, Sq j i)
            ≤ ∑ j ∈ Finset.range ny, ∑ i ∈ Finset.range nx,
                ENNReal.ofReal (K * (q / r) ^ (1 + d)) * ν (piece r ⁻¹' {b}) :=
              Finset.sum_le_sum fun j _ =>
                (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => hsq j i)
          _ = ENNReal.ofReal (ny * nx * (K * (q / r) ^ (1 + d))) * ν (piece r ⁻¹' {b}) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ny * nx),
                ENNReal.ofReal_mul (Nat.cast_nonneg ny), ENNReal.ofReal_natCast,
                ENNReal.ofReal_natCast]
              ring
      -- sum over the cover
      refine (measure_mono hsub).trans ?_
      have hstep : ν (⋃ τ ∈ Tb, ⋃ v ∈ Vb,
          ⋃ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ), Q σ) ≤
          ∑ τ ∈ Tb, ∑ v ∈ Vb, ∑ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ),
            ENNReal.ofReal (ny * nx * (K * (q / r) ^ (1 + d))) * ν (piece r ⁻¹' {b}) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
        exact hQ σ
      refine hstep.trans ?_
      -- each inner filter has fewer than θ elements
      have hfilt : ∀ τ v, (((Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ)).card : ℝ) ≤ θ := by
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
            ENNReal.ofReal (ny * nx * (K * (q / r) ^ (1 + d))) * ν (piece r ⁻¹' {b}) ≤
          ENNReal.ofReal (θ * (ny * nx * (K * (q / r) ^ (1 + d)))) * ν (piece r ⁻¹' {b}) := by
        intro τ _ v _
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        exact hfilt τ v
      calc ∑ τ ∈ Tb, ∑ v ∈ Vb,
            ∑ σ ∈ (Bτ τ).filter (fun σ => v ∈ Lf σ ∧ (cnt τ v : ℝ) < θ),
              ENNReal.ofReal (ny * nx * (K * (q / r) ^ (1 + d))) * ν (piece r ⁻¹' {b})
          ≤ ∑ τ ∈ Tb, ∑ v ∈ Vb,
              ENNReal.ofReal (θ * (ny * nx * (K * (q / r) ^ (1 + d)))) * ν (piece r ⁻¹' {b}) :=
            Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun v hv => hreal τ hτ v hv
        _ = ENNReal.ofReal (Tb.card * (Vb.card * (θ * (ny * nx * (K * (q / r) ^ (1 + d)))))) *
              ν (piece r ⁻¹' {b}) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            simp only [ENNReal.ofReal_natCast]
            ring
        _ ≤ ENNReal.ofReal C * ν (piece r ⁻¹' {b}) := by
            gcongr
            -- the real inequality
            have hny : (ny : ℝ) ≤ 2 * (2 * r) / q + 1 := para_rows_le hq (by positivity)
            have hnx : (nx : ℝ) ≤ 2 * K + 2 := para_cols_le hK0
            have hθe : θ * (q / r) ^ (1 + d) = (q / r) / Kpop := by
              rw [hθ, Real.rpow_add (by positivity), Real.rpow_one, Real.div_rpow hr.le hq.le,
                Real.div_rpow hq.le hr.le]
              field_simp
            have hrows : (2 * (2 * r) / q + 1) * (q / r) ≤ 5 := by
              rw [add_mul, one_mul]
              have : 2 * (2 * r) / q * (q / r) = 4 := by field_simp; ring
              rw [this]
              have : q / r ≤ 1 := (div_le_one hr).mpr hqr
              linarith
            have hδS : 2 * δS / r + 2 = 4 * K + 8 := by
              simp only [δS]; field_simp; ring
            have e1 : (Tb.card : ℝ) * (Vb.card * (θ * (ny * nx * (K * (q / r) ^ (1 + d))))) =
                Tb.card * Vb.card * nx * K * (ny * (θ * (q / r) ^ (1 + d))) := by ring
            rw [e1, hθe]
            have hny' : (ny : ℝ) * ((q / r) / Kpop) ≤ 5 / Kpop := by
              rw [mul_div_assoc', div_le_div_iff_of_pos_right hKpop]
              calc (ny : ℝ) * (q / r) ≤ (2 * (2 * r) / q + 1) * (q / r) := by gcongr
                _ ≤ 5 := hrows
            calc (Tb.card : ℝ) * Vb.card * nx * K * (ny * (q / r / Kpop))
                ≤ (4 * K + 8) * (2 * (CJ * r) / w + 2) * (2 * K + 2) * K * (5 / Kpop) := by
                  rw [← hδS]; gcongr
              _ ≤ C := by
                  rw [hC]
                  have h1 : 4 * K + 8 ≤ 12 * K := by linarith
                  have h2 : 2 * K + 2 ≤ 4 * K := by linarith
                  have h3 : 2 * (CJ * r) / w + 2 = 2 * (CJ * r / w + 1) := by ring
                  rw [h3]
                  have hX : 0 ≤ CJ * r / w + 1 := by positivity
                  calc (4 * K + 8) * (2 * (CJ * r / w + 1)) * (2 * K + 2) * K * (5 / Kpop)
                      ≤ (12 * K) * (2 * (CJ * r / w + 1)) * (4 * K) * K * (5 / Kpop) := by
                        gcongr
                    _ = 480 * K ^ 3 * (CJ * r / w + 1) / Kpop := by ring
    -- sum over pieces
    have hcov : Bad ⊆ ⋃ b : Fin 5 → ℤ, Bad ∩ piece r ⁻¹' {b} := by
      intro l hl; exact mem_iUnion.mpr ⟨piece r l, hl, rfl⟩
    have hdisj : Pairwise (Function.onFun Disjoint fun b : Fin 5 → ℤ => piece r ⁻¹' {b}) := by
      intro b b' hbb'
      exact Disjoint.preimage _ (disjoint_singleton.mpr hbb')
    have hmeas : ∀ b : Fin 5 → ℤ, MeasurableSet (piece r ⁻¹' {b}) :=
      fun b => hSN.measurable_piece r (measurableSet_singleton b)
    have hprob := hSN.prob
    calc ν Bad ≤ ∑' b : Fin 5 → ℤ, ν (Bad ∩ piece r ⁻¹' {b}) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ ≤ ∑' b : Fin 5 → ℤ, ENNReal.ofReal C * ν (piece r ⁻¹' {b}) := ENNReal.tsum_le_tsum hpiece
      _ = ENNReal.ofReal C * ν (⋃ b : Fin 5 → ℤ, piece r ⁻¹' {b}) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
      _ ≤ ENNReal.ofReal C * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal C := mul_one _

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
