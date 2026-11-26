import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.R1 of Erdős Problem 30
-- Credit: @kenanwienberg
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Erdős Problem 30

Erdős Problem 30 asks whether for every $\varepsilon > 0$,
$$h(N) = \sqrt{N} + O_\varepsilon(N^\varepsilon),$$
where $h(N)$ is the maximum size of a Sidon set in $\{1, \dots, N\}$.

Inside this reduction we prove **Bose's theorem (1942)**: for every prime power $q$, there is a
Sidon set of size $q$ in $\{1, \dots, q^2 - 1\}$, so $h(q^2 - 1) \ge q$. Using this construction
together with the elementary upper bound `Erdos30.erdos_30.variants.lindstrom_weak`, we reduce
Erdős Problem 30 to two independent conjectures from analytic number theory and additive
combinatorics:

- `H1`: Subpolynomial prime power gaps — for every $\varepsilon > 0$, every sufficiently large $n$
  admits a prime power $q \in [n - n^\varepsilon, n]$.
- `H2`: Subpolynomial Sidon diameter lower bound — for every $\varepsilon > 0$, every sufficiently
  large finite Sidon set $A \subset \mathbb{N}$ has diameter at least $|A|^2 - |A|^{1 + \varepsilon}$.
-/

namespace OMA.R_Erdos30_erdos_30_R1

open Filter
open scoped Asymptotics

/-- Subpolynomial prime power gaps: for every `ε > 0`, eventually every `n` has a prime power `q`
in `[n - n ^ ε, n]`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    ∃ q : ℕ, IsPrimePow q ∧ (n : ℝ) - (n : ℝ) ^ ε ≤ (q : ℝ) ∧ q ≤ n

/-- Subpolynomial Sidon diameter lower bound: for every `ε > 0`, every sufficiently large finite
Sidon set `A ⊆ ℕ` has two elements at distance at least `|A| ^ 2 - |A| ^ (1 + ε)`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ A : Finset ℕ, IsSidon (A : Set ℕ) → K ≤ A.card →
    ∃ a ∈ A, ∃ b ∈ A, (A.card : ℝ) ^ 2 - (A.card : ℝ) ^ (1 + ε) ≤ (b : ℝ) - (a : ℝ)

lemma card_le_h {N : ℕ} {A : Finset ℕ} (hS : IsSidon (A : Set ℕ))
    (hA : A ⊆ Finset.Icc 1 N) : A.card ≤ Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hS⟩)

lemma h_mono {M N : ℕ} (hMN : M ≤ N) : Erdos30.h M ≤ Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  apply Finset.sup_mono
  intro B hB
  rw [Finset.mem_filter, Finset.mem_powerset] at hB ⊢
  exact ⟨hB.1.trans (Finset.Icc_subset_Icc_right hMN), hB.2⟩

lemma exists_sidon_card_eq_h (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  set S := (Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)
  have hne : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro i₁ hi₁
    simp at hi₁
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hmax.symm⟩

/-- Bose's theorem (1942): for every prime power `q`, there exists a Sidon set of size `q`
contained in `{1, ..., q ^ 2 - 1}`, hence `q ≤ Erdos30.h (q ^ 2 - 1)`. -/
theorem bose_sidon {q : ℕ} (hq : IsPrimePow q) : q ≤ Erdos30.h (q ^ 2 - 1) := by
  classical
  rw [isPrimePow_nat_iff] at hq
  obtain ⟨p, r, hp, hr, hpr⟩ := hq
  have : Fact p.Prime := ⟨hp⟩
  let L := GaloisField p (2 * r)
  let : Fintype L := Fintype.ofFinite (GaloisField p (2 * r))
  have h2r : 2 * r ≠ 0 := by omega
  have hcardL : Nat.card L = q ^ 2 := by
    rw [GaloisField.card p (2 * r) h2r, ← hpr, ← pow_mul, mul_comm]
  have hq2 : 2 ≤ q := by
    rw [← hpr]
    exact le_trans hp.two_le (Nat.le_self_pow hr.ne' p)
  have hcardU : Nat.card Lˣ = q ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardL]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hg_pow_ne : (g : L) ^ q ≠ (g : L) := by
    intro heq
    have h1 : g ^ (q - 1) = 1 := by
      apply Units.ext
      have hmul : (g : L) ^ (q - 1) * (g : L) = 1 * (g : L) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), heq, one_mul]
      exact mul_right_cancel₀ g.ne_zero (by simpa using hmul)
    have hdvd : orderOf g ∣ q - 1 := orderOf_dvd_of_pow_eq_one h1
    have hle : orderOf g ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
    rw [hord] at hle
    have hq_sq : 1 ≤ q ^ 2 := by nlinarith
    have hle' : q ^ 2 ≤ q := by omega
    nlinarith
  have hadd_pow : ∀ x y : L, (x + y) ^ q = x ^ q + y ^ q := by
    intro x y
    rw [← hpr, add_pow_char_pow]
  let F : Finset L := insert 0 ((Finset.range (q - 1)).image fun k ↦ (((g ^ (q + 1)) ^ k : Lˣ) : L))
  have hF_fix : ∀ c ∈ F, c ^ q = c := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_image] at hc
    rcases hc with rfl | ⟨k, _, rfl⟩
    · exact zero_pow (by omega)
    · have hbase : (g ^ (q + 1)) ^ q = g ^ (q + 1) := by
        rw [← pow_mul]
        have hexp : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
          zify [show 1 ≤ q ^ 2 by nlinarith]
          ring
        rw [hexp, pow_add, ← hord, pow_orderOf_eq_one, one_mul]
      have hpow : ((g ^ (q + 1)) ^ k) ^ q = (g ^ (q + 1)) ^ k := by
        rw [← pow_mul, mul_comm k q, pow_mul, hbase]
      exact_mod_cast congrArg Units.val hpow
  have hF_card : F.card = q := by
    have h0 : (0 : L) ∉ (Finset.range (q - 1)).image fun k ↦ (((g ^ (q + 1)) ^ k : Lˣ) : L) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro k _ hk
      exact Units.ne_zero _ hk
    rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn]
    · rw [Finset.card_range]
      omega
    · intro k₁ hk₁ k₂ hk₂ heq
      rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
      wlog hle : k₁ ≤ k₂ generalizing k₁ k₂
      · exact (this hk₂ hk₁ heq.symm (by omega)).symm
      have hu : (g ^ (q + 1)) ^ k₁ = (g ^ (q + 1)) ^ k₂ := Units.ext heq
      have h1 : g ^ ((q + 1) * (k₂ - k₁)) = 1 := by
        rw [pow_mul]
        have hmul : (g ^ (q + 1)) ^ k₁ * (g ^ (q + 1)) ^ (k₂ - k₁) = (g ^ (q + 1)) ^ k₁ * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, hu]
        exact mul_left_cancel hmul
      have hdvd : q ^ 2 - 1 ∣ (q + 1) * (k₂ - k₁) := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one h1
      have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
        zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
        ring
      rw [hfac] at hdvd
      have hdvd' : q - 1 ∣ k₂ - k₁ := (Nat.mul_dvd_mul_iff_left (by omega)).mp hdvd
      have hzero : k₂ - k₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
      omega
  have hne_zero : ∀ c ∈ F, (g : L) + c ≠ 0 := by
    intro c hc hzero
    have h1 : ((g : L) + c) ^ q = 0 := by rw [hzero, zero_pow (by omega)]
    rw [hadd_pow, hF_fix c hc] at h1
    apply hg_pow_ne
    linear_combination h1 - hzero
  have hex_log : ∀ c ∈ F, ∃ a ∈ Finset.Icc 1 (q ^ 2 - 1), (g : L) ^ a = (g : L) + c := by
    intro c hc
    let u : Lˣ := Units.mk0 ((g : L) + c) (hne_zero c hc)
    obtain ⟨m, hm⟩ := hg u
    have hpos : 0 < orderOf g := by
      rw [hord]
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have hfin : ∃ k : ℕ, k < orderOf g ∧ g ^ k = u := by
      refine ⟨(m % (orderOf g : ℤ)).toNat, ?_, ?_⟩
      · have hlt := Int.emod_lt_of_pos m (Int.natCast_pos.mpr hpos)
        have hnn := Int.emod_nonneg m (Int.natCast_ne_zero.mpr hpos.ne')
        omega
      · have hnn := Int.emod_nonneg m (Int.natCast_ne_zero.mpr hpos.ne')
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]
        exact hm
    obtain ⟨k, hk, hgk⟩ := hfin
    rw [hord] at hk
    by_cases hk0 : k = 0
    · refine ⟨q ^ 2 - 1, Finset.mem_Icc.mpr ⟨by rw [← hord]; omega, le_rfl⟩, ?_⟩
      have hu1 : u = 1 := by rw [← hgk, hk0, pow_zero]
      have hg1 : g ^ (q ^ 2 - 1) = 1 := by rw [← hord, pow_orderOf_eq_one]
      have := congrArg Units.val (hg1.trans hu1.symm)
      simpa [u] using this
    · refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have := congrArg Units.val hgk
      simpa [u] using this
  let f : L → ℕ := fun c ↦ if hc : c ∈ F then Classical.choose (hex_log c hc) else 0
  have hf_mem : ∀ c ∈ F, f c ∈ Finset.Icc 1 (q ^ 2 - 1) := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (Classical.choose_spec (hex_log c hc)).1
  have hf_pow : ∀ c ∈ F, (g : L) ^ f c = (g : L) + c := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (Classical.choose_spec (hex_log c hc)).2
  let A : Finset ℕ := F.image f
  have hA_sub : A ⊆ Finset.Icc 1 (q ^ 2 - 1) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact hf_mem c hc
  have hA_card : A.card = q := by
    rw [Finset.card_image_of_injOn, hF_card]
    intro c₁ hc₁ c₂ hc₂ heq
    have h1 := hf_pow c₁ hc₁
    have h2 := hf_pow c₂ hc₂
    rw [heq] at h1
    exact add_left_cancel (h1.symm.trans h2)
  have hA_sidon : IsSidon (A : Set ℕ) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    simp only [A, Finset.mem_coe, Finset.mem_image] at ha₁ hb₁ ha₂ hb₂
    obtain ⟨c₁, hc₁, rfl⟩ := ha₁
    obtain ⟨d₁, hd₁, rfl⟩ := hb₁
    obtain ⟨c₂, hc₂, rfl⟩ := ha₂
    obtain ⟨d₂, hd₂, rfl⟩ := hb₂
    have hprod : ((g : L) + c₁) * ((g : L) + c₂) = ((g : L) + d₁) * ((g : L) + d₂) := by
      rw [← hf_pow c₁ hc₁, ← hf_pow c₂ hc₂, ← hf_pow d₁ hd₁, ← hf_pow d₂ hd₂,
        ← pow_add, ← pow_add, hsum]
    have hlin : (c₁ + c₂) * (g : L) + c₁ * c₂ = (d₁ + d₂) * (g : L) + d₁ * d₂ := by
      linear_combination hprod
    have hlin_q : (c₁ + c₂) * (g : L) ^ q + c₁ * c₂ = (d₁ + d₂) * (g : L) ^ q + d₁ * d₂ := by
      have h := congrArg (fun x : L ↦ x ^ q) hlin
      simp only [hadd_pow, mul_pow, hF_fix c₁ hc₁, hF_fix c₂ hc₂, hF_fix d₁ hd₁, hF_fix d₂ hd₂] at h
      exact h
    have hdiff : (c₁ + c₂ - (d₁ + d₂)) * ((g : L) ^ q - (g : L)) = 0 := by
      linear_combination hlin_q - hlin
    have hsum_c : c₁ + c₂ = d₁ + d₂ := by
      rcases mul_eq_zero.mp hdiff with h | h
      · exact sub_eq_zero.mp h
      · exact (hg_pow_ne (sub_eq_zero.mp h)).elim
    have hprod_c : c₁ * c₂ = d₁ * d₂ := by
      linear_combination hlin - (g : L) * hsum_c
    have hquad : (c₁ - d₁) * (c₁ - d₂) = 0 := by
      linear_combination c₁ * hsum_c - hprod_c
    rcases mul_eq_zero.mp hquad with h | h
    · have h1 : c₁ = d₁ := sub_eq_zero.mp h
      have h2 : c₂ = d₂ := by linear_combination hsum_c - h1
      exact Or.inl ⟨congrArg f h1, congrArg f h2⟩
    · have h1 : c₁ = d₂ := sub_eq_zero.mp h
      have h2 : c₂ = d₁ := by linear_combination hsum_c - h1
      exact Or.inr ⟨congrArg f h1, congrArg f h2⟩
  calc
    q = A.card := hA_card.symm
    _ ≤ Erdos30.h (q ^ 2 - 1) := card_le_h hA_sidon hA_sub

lemma lower_bound_of_H1 (h1 : H1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ).sqrt - (Erdos30.h N : ℝ) ≤ 2 * (N : ℝ) ^ ε := by
  have hgap := h1 (2 * ε) (by linarith)
  rw [Filter.eventually_atTop] at hgap ⊢
  obtain ⟨M₀, hM₀⟩ := hgap
  refine ⟨max (M₀ ^ 2) 1, fun N hN ↦ ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNM : M₀ ^ 2 ≤ N := le_trans (le_max_left _ _) hN
  set m := Nat.sqrt N
  have hm_ge : M₀ ≤ m := Nat.le_sqrt.mpr (by simpa [sq] using hNM)
  obtain ⟨q, hq_pp, hq_lo, hq_le⟩ := hM₀ m hm_ge
  have hq_sq : q ^ 2 - 1 ≤ N := by
    have h1 : q ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hq_le 2
    have h2 : m ^ 2 ≤ N := by simpa [sq] using Nat.sqrt_le N
    omega
  have hh_ge : q ≤ Erdos30.h N := le_trans (bose_sidon hq_pp) (h_mono hq_sq)
  have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg m) (Nat.cast_nonneg N)]
    exact_mod_cast (by simpa [sq] using Nat.sqrt_le N : m ^ 2 ≤ N)
  have hsqrt_lt : Real.sqrt (N : ℝ) < (m : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have hlt : N < (m + 1) * (m + 1) := Nat.lt_succ_sqrt N
    have hlt' : (N : ℝ) < ((m : ℝ) + 1) ^ 2 := by
      have : (N : ℝ) < ((m + 1) * (m + 1) : ℕ) := by exact_mod_cast hlt
      push_cast at this
      nlinarith
    exact hlt'
  have hm_pow : (m : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ ε := by
    calc
      (m : ℝ) ^ (2 * ε) ≤ (Real.sqrt (N : ℝ)) ^ (2 * ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg m) hm_le_sqrt (by linarith)
      _ = ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 * ε) := by rw [Real.sqrt_eq_rpow]
      _ = (N : ℝ) ^ ((1 : ℝ) / 2 * (2 * ε)) := by rw [← Real.rpow_mul (Nat.cast_nonneg N)]
      _ = (N : ℝ) ^ ε := by ring_nf
  have hN_pow_ge : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hN1) hε.le
  have hh_ge_r : (q : ℝ) ≤ (Erdos30.h N : ℝ) := by exact_mod_cast hh_ge
  linarith

lemma upper_bound_of_H2 (h2 : H2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (Erdos30.h N : ℝ) - (N : ℝ).sqrt ≤ 3 * (N : ℝ) ^ ε := by
  set δ : ℝ := min ε (1 / 4)
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_q : δ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨K, hK⟩ := h2 (2 * δ) (by linarith)
  rw [Filter.eventually_atTop]
  refine ⟨max (K ^ 2) 1, fun N hN ↦ ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNK : K ^ 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN_pos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN_pow_ge : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN_pos hε.le
  by_cases hhK : Erdos30.h N < K
  · have hK_le : (K : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg K) (Nat.cast_nonneg N)]
      exact_mod_cast hNK
    have hh_le : (Erdos30.h N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hhK.le
    linarith
  · push Not at hhK
    obtain ⟨A, hA_sub, hA_sidon, hA_card⟩ := exists_sidon_card_eq_h N
    have hKA : K ≤ A.card := by rwa [hA_card]
    obtain ⟨a, ha, b, hb, hdiam⟩ := hK A hA_sidon hKA
    have ha_mem := Finset.mem_Icc.mp (hA_sub ha)
    have hb_mem := Finset.mem_Icc.mp (hA_sub hb)
    have hba_le : (b : ℝ) - (a : ℝ) ≤ (N : ℝ) := by
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_mem.1
      have hbN : (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast hb_mem.2
      linarith
    set k : ℕ := Erdos30.h N
    rw [hA_card] at hdiam
    have hk_sq : (k : ℝ) ^ 2 - (k : ℝ) ^ (1 + 2 * δ) ≤ (N : ℝ) := le_trans hdiam hba_le
    by_cases hk0 : k = 0
    · simp only [hk0, Nat.cast_zero]
      have hsq_nn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      linarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        have : 1 ≤ k := Nat.pos_of_ne_zero hk0
        exact_mod_cast this
      have hk_rpow_le : (k : ℝ) ^ (4 * δ) ≤ (k : ℝ) ^ (1 + 2 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      have hk_mul : (k : ℝ) * (k : ℝ) ^ (2 * δ) = (k : ℝ) ^ (1 + 2 * δ) := by
        rw [Real.rpow_add (by linarith : (0 : ℝ) < k), Real.rpow_one]
      have hk_sq_rpow : ((k : ℝ) ^ (2 * δ)) ^ 2 = (k : ℝ) ^ (4 * δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        ring_nf
      have hcomp : ((k : ℝ) - (k : ℝ) ^ (2 * δ)) ^ 2 ≤ (N : ℝ) := by
        have hexp : ((k : ℝ) - (k : ℝ) ^ (2 * δ)) ^ 2 =
            (k : ℝ) ^ 2 - 2 * ((k : ℝ) * (k : ℝ) ^ (2 * δ)) + ((k : ℝ) ^ (2 * δ)) ^ 2 := by ring
        rw [hexp, hk_mul, hk_sq_rpow]
        linarith
      have hdiff_le : (k : ℝ) - (k : ℝ) ^ (2 * δ) ≤ Real.sqrt (N : ℝ) := by
        by_cases hsign : (k : ℝ) - (k : ℝ) ^ (2 * δ) ≤ 0
        · exact le_trans hsign (Real.sqrt_nonneg _)
        · push Not at hsign
          rw [Real.le_sqrt hsign.le (Nat.cast_nonneg N)]
          exact hcomp
      have hA_range : A ⊆ Finset.range (N + 1) := by
        intro x hx
        have := Finset.mem_Icc.mp (hA_sub hx)
        exact Finset.mem_range.mpr (by omega)
      have hlind := Erdos30.erdos_30.variants.lindstrom_weak A N hA_sidon hA_range
      rw [hA_card] at hlind
      have hk_le_3sqrt : (k : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
        have hsqrt2N : ((Nat.sqrt (2 * N) : ℕ) : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := by
          rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
          have : (Nat.sqrt (2 * N)) ^ 2 ≤ 2 * N := by simpa [sq] using Nat.sqrt_le (2 * N)
          exact_mod_cast this
        have hsqrt2 : Real.sqrt (2 * (N : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
          rw [Real.sqrt_mul (by norm_num)]
          have : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_left (by norm_num)]
            norm_num
          nlinarith [Real.sqrt_nonneg (N : ℝ)]
        have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
          rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)]
          nlinarith
        have hlind_r : (k : ℝ) ≤ (Nat.sqrt (2 * N) : ℝ) + 1 := by exact_mod_cast hlind
        linarith
      have hk_pow_le : (k : ℝ) ^ (2 * δ) ≤ 3 * (N : ℝ) ^ ε := by
        have h3_pow : (3 : ℝ) ^ (2 * δ) ≤ 3 := by
          calc
            (3 : ℝ) ^ (2 * δ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 3 := Real.rpow_one 3
        have hN_δ_ε : (N : ℝ) ^ δ ≤ (N : ℝ) ^ ε :=
          Real.rpow_le_rpow_of_exponent_le hN_pos hδ_le_ε
        calc
          (k : ℝ) ^ (2 * δ) ≤ (3 * Real.sqrt (N : ℝ)) ^ (2 * δ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg k) hk_le_3sqrt (by linarith)
          _ = (3 : ℝ) ^ (2 * δ) * (Real.sqrt (N : ℝ)) ^ (2 * δ) :=
            Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _)
          _ = (3 : ℝ) ^ (2 * δ) * ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 * δ) := by
            rw [Real.sqrt_eq_rpow]
          _ = (3 : ℝ) ^ (2 * δ) * (N : ℝ) ^ δ := by
            rw [← Real.rpow_mul (Nat.cast_nonneg N)]
            ring_nf
          _ ≤ 3 * (N : ℝ) ^ ε := by
            have hnn : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg N) _
            nlinarith
      linarith

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30 := by
  intro h1 h2 ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [lower_bound_of_H1 h1 hε, upper_bound_of_H2 h2 hε,
    Filter.eventually_ge_atTop (1 : ℕ)] with N hlo hup hN1
  have hpow_nn : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow_nn, abs_le]
  constructor <;> linarith

end OMA.R_Erdos30_erdos_30_R1
