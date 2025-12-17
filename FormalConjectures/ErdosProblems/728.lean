/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 728

*Reference:* [erdosproblems.com/728](https://www.erdosproblems.com/728)
-/

namespace Erdos728

#eval Nat.digits 3  <|2^15
/-!
Notum est hanc quantitatem $a^n+1$ semper habere divisores, quoties $n$ sit numerus impar
vel per imparem praeter unitatem divisibilis.
Namque $a^{2m+1}+1$ dividi potest per $a+1$...
-/
theorem divisibilitas_impar (a m : ℕ) :
    (a + 1) ∣ (a ^ (2 * m + 1) + 1) := by
  convert (Odd.nat_add_dvd_pow_add_pow a 1 ⟨m, rfl⟩)
  norm_num

/-!
...et $a^{p(2m+1)}+1$ per $a^p+1$, quicunque etiam numerus loco $a$ substituatur.
-/
theorem divisibilitas_generalis (a m p : ℕ) :
    (a ^ p + 1) ∣ (a ^ (p * (2 * m + 1)) + 1) := by
  have := Odd.nat_add_dvd_pow_add_pow (a^p) 1 ⟨m, rfl⟩
  rwa [pow_mul,one_pow] at *


/-!
Quamobrem si qui sunt numeri primi huius formae $a^n+1$, ii omnes comprehendantur necesse est
in hac forma $a^{2^m}+1$.
-/
theorem forma_numerorum_primorum (a n : ℕ) (h_prime : (a ^ n + 1).Prime) (ha: 1 < a) (hn: 1 < n) :
    ∃ m : ℕ, n = 2 ^ m := by
  by_contra hm
  simp at hm
  have : ∃ m > 0, ∃ p > 1, n = p * (2 * m + 1) := by
    convert (by_contra fun and=>hm _ (n.prod_primeFactorsList hn.ne_bot▸List.prod_eq_pow_card _ _ fun A B=>_))
    convert(n.prime_of_mem_primeFactorsList B).eq_two_or_odd.resolve_right ((n.dvd_of_mem_primeFactorsList B).elim fun and R M=>absurd (h_prime.eq_one_or_self_of_dvd (a^and + 1)) _)
    exact (mt (. ( ((Nat.odd_iff.2 M).nat_add_dvd_pow_add_pow _ _).trans (by rw [ R,pow_mul',one_pow]))) (by field_simp [ha.ne', R,(n.prime_of_mem_primeFactorsList B).ne_one, right_ne_zero_of_mul (R▸hn).ne_bot]))
  obtain ⟨m, hm, p, hp, h⟩ := this
  have := divisibilitas_generalis a m p
  rw [←h] at this
  have h0 : 2  ≤ a ^ p + 1 := by
    exact (Nat.succ_lt_succ (a.pow_pos ha.le))
  have h1 :  a ^ p + 1 < a ^ n + 1 := by
    field_simp only [lt_mul_right,h,a.pow_lt_pow_right,Nat.succ_lt_succ,Nat.lt_add_of_pos_left]
  absurd h_prime
  exact Nat.not_prime_of_dvd_of_lt this h0 h1

/-!
Neque tamen ex hoc potest concludi $a^{2^m}+1$ semper exhibere numerum primum, quicquid sit $a$;
primo enim perspicuum est, si $a$ sit numerus impar, istam formam divisorem habiturum $2$.
-/
theorem exception_impar (a m : ℕ) (h_odd : Odd a) :
    2 ∣ (a ^ (2 ^ m) + 1) := by
  exact (h_odd.pow.add_one).two_dvd

/-!
Deinde quoque, etiamsi $a$ denotet numerum parem, innumeri tamen dantur casus, quibus numerus
compositus prodit. Ita haec saltem formula $a^2+1$ potest dividi per $5$, quoties est $a=5b\pm3$, ...
-/
example (b : ℕ) : 5 ∣ ((5 * b + 3) ^ 2 + 1) := by
  use b * (b * 5 + 6) + 2
  ring

example (b : ℤ) : 5 ∣ ((5 * b - 3) ^ 2 + 1) := by
  use b * (b * 5 - 6) + 2
  ring

/-!
... et $30^2+1$ potest dividi per $17$,...
-/
example : 17 ∣ (30 ^ 2 + 1) := by decide

/-!
... et $50^2+1$ per $41$.
-/
example :  41 ∣ (50 ^ 2 + 1) := by decide

/-!
Simili modo $10^4+1$ habet divisorem $73$, ...
-/
example : 73 ∣ (10 ^ 4 + 1) := by decide

/-!
... $6^8+1$ habet divisorem $17$ ...
-/
example : 17 ∣ (6 ^ 8 + 1) := by decide

/-!
.. et $6^{128}+1$ est divisibilis per $257$.
-/
example : 257 ∣ (6 ^ 128 + 1) := by norm_num

/-!
At huius formae $2^m+1$ quantum ex tabulis numerorum primorum, quae quidem non ultra 100000
extenduntur, nullus detegitur casus, quo divisor aliquis locum habeat.
-/
theorem observatio_tabularum (k : ℕ) (hk_bound : k < 100000) :
    (∃ n, k = 2 ^ (2 ^ n) + 1) → k.Prime := by
  rintro ⟨n, rfl⟩
  have : 2 ^ (2 ^ n) < 2 ^ (2 ^ 5) := by omega
  have h_n_lt_5 : n < 5 := by
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp this
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  interval_cases n <;> norm_num


/-!
Sed nescio, quo fato eveniat, ut statim sequens, nempe $2^{2^5} + 1$, cesset esse numerus primus.
Observavi enim his diebus longe alia agens posse hunc numerum dividi per $641$, ut cuique
tentanti statim patebit.
-/
theorem sequens_non_primus : ¬ (2 ^ (2 ^ 5) + 1).Prime := by
  rw [Nat.prime_def_lt]
  push_neg
  norm_num
  use 641
  norm_num

/-!
Est enim $2^{2^5} + 1 = 2^{32} + 1 = 4294967297$.
-/
example : 2 ^ (2 ^ 5) + 1 = 4294967297 := by norm_num

/-!
Ex quo intelligi potest theorema hoc etiam in aliis, qui sequuntur, casibus fallere et hanc
ob rem problema de inveniendo numero primo quovis dato maiore etiam nunc non esse solutum.
-/
theorem fallacia_conjecturae : ¬ (∀ n, (2 ^ (2 ^ n) + 1).Prime) := by
  push_neg
  use 5
  exact sequens_non_primus

/-!
Considerabo nunc etiam formulam $2^n - 1$, quae, quoties $n$ non est numerus primus, habet
divisores, ...
-/
theorem si_n_compositus_mersennus_compositus (n : ℕ) (h : ¬ n.Prime) (hn : 1 < n) :
    ¬ (2 ^ n - 1).Prime := by
  refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
  · exact (2).le_pred_of_lt (lt_self_pow₀ (by decide) hn)
  · have : ∃ x > 1, ∃ y > 1, x < n ∧ y < n ∧ n = x * y := by
      sorry
    obtain ⟨x, hx1, y, hy1, hxn, hyn, h_prod⟩ := this
    use 2^x - 1
    sorry


/-!
... neque tantum $2^n - 1$, sed etiam $a^n - 1$.
-/
theorem si_n_compositus_compositus (n a : ℕ) (h : ¬ n.Prime) (hn : 1 < n) (ha : 1 < a):
    ¬ (a ^ n - 1).Prime := by
  refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
  · exact (Nat.lt_pow_self ha).le_pred.trans' hn
  · have : ∃ x > 1, ∃ y > 1, x < n ∧ y < n ∧ n = x * y := by
      sorry
    obtain ⟨x, hx1, y, hy1, hxn, hyn, h_prod⟩ := this
    use a^x - 1
    sorry


/-!
Sed si $n$ sit numerus primus, videri posset etiam $2^n - 1$ semper talem exhibere: hoc tamen
asseverare nemo est ausus, cum tam facile potuisset refelli.
-/
theorem non_omnis_mersennus_primus : ¬ (∀ n, n.Prime → (2 ^ n - 1).Prime) := by
  push_neg
  use 11
  norm_num

/-!
Namque $2^{11} - 1$ i. e. $2047$ divisores habet $23$ ...
-/
theorem exm : (2 ^ 11 - 1).primeFactors = {23, 89} := by
  simp [Nat.primeFactors]

/-!
... et $89$ et $2^{23} - 1$ dividi potest per $47$.
-/
example : 47 ∣ (2 ^ 23 - 1) := by norm_num

/-!
Video autem Cel. Wolfium non solum hoc in Elem. Matheseos editione altera non advertisse, ubi
numeros perfectos investigat atque $2047$ inter primos numerat, sed etiam $511$ seu $2^9 - 1$
pro tali habet, cum tamen sit divisibilis per $2^3 - 1$ i.e. $7$.
-/
theorem errores_wolfii : ¬ (2047).Prime ∧ ¬ (511).Prime ∧ (2^3 - 1) ∣ (2^9 - 1) := by
  norm_num

/-!
Dat autem $2^{n-1}(2^n - 1)$ numerum perfectum, quoties $2^n - 1$ est primus, ...
-/
theorem generatio_perfecti (n : ℕ) (h_prime : (2 ^ n - 1).Prime) :
    ((2 ^ (n - 1) * (2 ^ n - 1))).Perfect := by
  constructor
  · refine add_right_cancel ((Nat.sum_divisors_eq_sum_properDivisors_add_self).symm.trans (.trans ( ((Nat.coprime_primes (by decide) (h_prime)).mpr (by cases n with omega)).pow_left _).sum_divisors_mul ?_))
    cases n with norm_num[*,mul_comm,Nat.succ_le,←two_mul,Nat.geomSum_eq,←mul_assoc,←pow_succ']
  · exact (Nat.mul_pos (n - 1).two_pow_pos) (h_prime).pos

/-!
... debet ergo etiam $n$ esse numerus primus.
-/
theorem necessitas_exponentis_primi (n : ℕ) (h_prime : (2 ^ n - 1).Prime) (hn : n ≠ 1) :
    n.Prime := by
  by_contra h_not_prime
  absurd h_prime
  apply si_n_compositus_mersennus_compositus n
  · exact h_not_prime
  · exact hn.symm.lt_of_le (by cases n with | zero => contradiction | succ n => omega)


/-!
Inveni autem hoc semper fieri, si sit $n = 4m - 1$, atque $8m - 1$ fuerit numerus primus,
tum enim $2^n - 1$ semper poterit dividi per $8m - 1$.
-/
theorem regula_divisoris_mersenni (m n : ℕ) (hm : m ≥ 1) (hn : n = 4 * m  - 1) (h_prime : (8 * m - 1).Prime) :
    (8 * m - 1) ∣ (2 ^ n - 1) := by
  sorry

/-!
Hinc excludendi sunt casus sequentes: 11, 23, 83, 131, 179, 191, 239, etc. qui numeri pro $n$
substituti reddunt $2^n - 1$ numerum compositum.
-/
theorem casus_excludendi :
    ¬ (2 ^ 11 - 1).Prime ∧
    ¬ (2 ^ 23 - 1).Prime ∧
    ¬ (2 ^ 83 - 1).Prime ∧
    ¬ (2 ^ 131 - 1).Prime ∧
    ¬ (2 ^ 179 - 1).Prime ∧
    ¬ (2 ^ 191 - 1).Prime ∧
    ¬ (2 ^ 239 - 1).Prime := by
  norm_num

/-!
Neque tamen reliqui numeri primi omnes loco $n$ positi satisfaciunt, sed plures insuper
excipiuntur; sic observavi $2^{37} - 1$ dividi posse per $223$...
-/
theorem divisio_37 : 223 ∣ (2 ^ 37 - 1) := by norm_num

/-!
... $2^{43} - 1$ per $431$...
-/
theorem divisio_43 : 431 ∣ (2 ^ 43 - 1) := by norm_num

/-!
... $2^{29} - 1$ per $1103$...
-/
theorem divisio_29 : 1103 ∣ (2 ^ 29 - 1) := by norm_num

/-!
... $2^{73} - 1$ per $439$, omnes tamen excludere non est in potestate.
-/
theorem divisio_13 : 439 ∣ (2 ^ 73 - 1) := by norm_num


/-!
## Theorema 1

Si fuerit $n$ numerus primus, omnes potentia exponentis $n-1$ per $n$ divisa vel nihil vel unitatem
relinquit.
-/
theorem theorema_1 (a n : ℕ) (hn : n.Prime) :
    ((a ^ (n - 1)) : ZMod n) ∈ ({0, 1} : Finset (ZMod n)) := by
  simp_all
  match Fact.mk @hn with | S=>exact (em (@_)).imp (by rw [·, zero_pow.comp (1).sub_ne_zero_of_lt @hn.one_lt]) (ZMod.pow_card_sub_one_eq_one)

/-!
## Theorema 2

Manente $n$ numero primo omnis potentia, cuius exponens est $n^{m-1}(n-1)$, divisa per $n^m$ vel $0$
vel $1$ relinquit.
-/
theorem theorema_2 (a n m : ℕ) (hn : n.Prime) (hm : m > 0) :
    (a ^ (n ^ (m - 1) * (n - 1)) : ZMod (n ^ m)) ∈ ({0, 1} : Finset (ZMod (n ^ m))) := by
  norm_num [pow_mul']
  by_cases h:IsUnit (a:ZMod (n^m))
  · use h.elim fun and true => true▸.inr (pow_mul and.1 _ _▸congr_arg Units.val (orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_of_pow_eq_one (ZMod.pow_totient _)|>.trans (?_))))
    rwa[n.totient_prime_pow hn,mul_comm]
  · rw_mod_cast[ZMod.natCast_zmod_eq_zero_iff_dvd,ZMod.isUnit_iff_coprime]at*
    exact (.inl ((pow_dvd_pow_of_dvd ((by_contra (h.comp (hn.coprime_iff_not_dvd.2 ·|>.symm.pow_right m))).pow hn.pred_pos.ne') _).trans (pow_dvd_pow _ (.trans (by valid) (Nat.lt_pow_self hn.one_lt)))))

/-!
## Theorema 3

Sint $m, n, p, q$ etc. numeri primi inaequales, sitque $A$ minimus communis dividuus eorum unitate
minutorum, puta ipsorum $m-1, n-1, p-1, q-1$ etc.; his positis dico omnem potentiam exponentis $A$
ut $a^A$ diuisam per $mnpq$ etc. vel $0$ vel $1$ relinquere, nisi $a$ dividi possit per aliquem
horum numerorum $m, n, p, q$ etc.
-/
theorem theorema_3 (primes : Finset ℕ) (h_primes : ∀ p ∈ primes, p.Prime) (a : ℕ) :
    -- minimus communis dividuus eorum unitate minutorum, puta ipsorum $m-1, n-1, p-1, q-1$ etc.
    let A := (primes.toList.map (fun n => n - 1)).toFinset.lcm id
    -- $mnpq$ etc.
    let P := ∏ p ∈ primes, p
    (∀ p ∈ primes, ¬ p ∣ a) → ((a ^ A) : ZMod P) ∈ ({0, 1} : Finset (ZMod P)):= by
  aesop
  use .inr (mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.modEq_of_dvd ((Nat.cast_prod _ _).dvd.trans (primes.prod_dvd_of_coprime (?_) ?_)))|>.trans Nat.cast_one)
  · use fun and a s R L=>((and.coprime_primes (h_primes and a) (h_primes ( s) R)).2 L).cast
  use fun R L=> (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by_contra (absurd (Fact.mk (h_primes R L)) fun and=>. (?_)))
  norm_num[orderOf_dvd_iff_pow_eq_one.1 ((ZMod.orderOf_dvd_card_sub_one _).trans ( show R-1 ∣A from Finset.dvd_lcm ↑_)),A,CharP.cast_eq_zero_iff _ R,Exists.intro R, *]

/-!
## Theorema 4

Denotante $2n+1$ numerum primum poterit $3^n+1$ dividi per $2n+1$, si sit vel $n=6p+2$ vel
$n=6p+3$; at $3^n-1$ dividi poterit per $2n+1$, si sit vel $n=6p$ vel $n=6p-1$.
-/
theorem theorema_4 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 6 * p + 2 ∨ n = 6 * p + 3) → 2 * n + 1 ∣ 3 ^ n + 1) ∧
    ((∃ p, n = 6 * p ∨ n = 6 * p - 1) → 2 * n + 1 ∣ 3 ^ n - 1) := by
  -- AlphaProof failed to close this goal
  sorry

/-!
## Theorema 5

$3^n+2^n$ potest dividi per $2n+1$, si sit $n=$ vel $12p+3$ vel $12p+5$ vel $12p+6$ vel $12p+8$.
Atque $3^n-2^n$ potest dividi per $2n+1$, si sit $n=$ vel $12p$ vel $12p+2$ vel $12p+9$ vel
$12p+11$.
-/
theorem theorema_5 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 12 * p + 3 ∨ n = 12 * p + 5 ∨ n = 12 * p + 6 ∨ n = 12 * p + 8) →
    2 * n + 1 ∣ 3 ^ n + 2 ^ n) ∧
    ((∃ p, n = 12 * p ∨ n = 12 * p + 2 ∨ n = 12 * p + 9 ∨ n = 12 * p + 11) →
    2 * n + 1 ∣ 3 ^ n - 2 ^ n) := by
  -- AlphaProof failed to close this goal
  sorry

/-!
## Theorema 6

Sub iisdem conditionibus, quibus $3^n+2^n$, poterit etiam $6^n+1$ dividi per $2n+1$; atque
$6^n-1$ sub iisdem, quibus $3^n-2^n$.
-/
theorem theorema_6 (n : ℕ) (h_prime : (2 * n + 1).Prime) :
    ((∃ p, n = 12 * p + 3 ∨ n = 12 * p + 5 ∨ n = 12 * p + 6 ∨ n = 12 * p + 8) →
    2 * n + 1 ∣ 6 ^ n + 1) ∧
    ((∃ p, n = 12 * p ∨ n = 12 * p + 2 ∨ n = 12 * p + 9 ∨ n = 12 * p + 11) →
    2 * n + 1 ∣ 6 ^ n - 1) := by
  -- AlphaProof failed to close this goal
  sorry




end Erdos728
