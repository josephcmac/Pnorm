(*
  File:    Pnorm.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
  Author:  Manuel Eberl, TU München
*)
section \<open>p-adic valuation and p-adic norm\<close>
theory Pnorm

imports 
  "HOL-Number_Theory.Number_Theory"

begin

text \<open>
  Following ~\cite{koblitz2012p}, we define the p-adic valuation @{text pval}, the p-adic norm 
  @{text pnorm} in a computational way. We prove their basic properties.
\<close>

subsection \<open>Unsorted\<close>

lemma quotient_of_int' [simp]: "quotient_of (of_int a) = (a, 1)"
  using Rat.of_int_def quotient_of_int by auto

lemma snd_quotient_of_nonzero [simp]: "snd (quotient_of x) \<noteq> 0"
  using quotient_of_denom_pos[of x "fst (quotient_of x)" "snd (quotient_of x)"] by simp

lemma fst_quotient_of_eq_0_iff [simp]: "fst (quotient_of x) = 0 \<longleftrightarrow> x = 0"
  by (metis divide_eq_0_iff fst_conv of_int_0 prod.collapse quotient_of_div quotient_of_int')

lemma multiplicity_int_int [simp]: "multiplicity (int a) (int b) = multiplicity a b"
  by (simp add: multiplicity_def flip: of_nat_power)

lemma multiplicity_add_absorb_left:
  assumes "multiplicity p x < multiplicity p y" "x \<noteq> 0"
  shows   "multiplicity p (x + y) = multiplicity p x"
proof (cases "y = 0 \<or> is_unit p")
  case False
  show ?thesis
  proof (rule multiplicity_eqI)
    from assms show "p ^ multiplicity p x dvd x + y"
      by (intro dvd_add) (auto intro!: multiplicity_dvd')
    show "\<not>p ^ Suc (multiplicity p x) dvd x + y" using assms False
      by (subst dvd_add_left_iff; subst power_dvd_iff_le_multiplicity) auto
  qed
qed (use assms in \<open>auto simp: multiplicity_unit_left\<close>)

lemma multiplicity_add_absorb_right:
  assumes "multiplicity p x > multiplicity p y" "y \<noteq> 0"
  shows   "multiplicity p (x + y) = multiplicity p y"
  using multiplicity_add_absorb_left[of p y x] assms by (simp add: add.commute)

lemma multiplicity_add_ge:
  assumes "x + y \<noteq> 0"
  shows   "multiplicity p (x + y) \<ge> min (multiplicity p x) (multiplicity p y)"
proof (cases "is_unit p \<or> x = 0 \<or> y = 0")
  case False
  thus ?thesis using assms
    by (intro multiplicity_geI dvd_add) (auto intro!: multiplicity_dvd')
qed (auto simp: multiplicity_unit_left)

lemma multiplicity_minus_right [simp]:
  "multiplicity a (-b :: 'a :: {factorial_semiring,comm_ring_1}) = multiplicity a b"
  by (simp add: multiplicity_def)

lemma multiplicity_minus_left [simp]:
  "multiplicity (-a :: 'a :: {factorial_semiring,comm_ring_1}) b = multiplicity a b"
  using multiplicity_times_unit_left[of "-1" a b] by simp


definition intpow :: "'a :: {inverse, power} \<Rightarrow> int \<Rightarrow> 'a" where 
  "intpow x n = (if n \<ge> 0 then x ^ nat n else inverse x ^ (nat (-n)))"

(* The option to the user to use the same notation as powr *)
notation intpow  (infixr "powi" 80)

lemma intpow_int [simp]: " x powi (int n) = x ^ n"
  by (simp add: intpow_def)

lemma intpow_minus [simp]: "intpow (x :: 'a :: field) (-int n) = inverse (intpow x n)"
  by (auto simp: intpow_def power_inverse)

lemma intpow_eq_0_iff [simp]: "intpow (x :: 'a :: field) n = 0 \<longleftrightarrow> x = 0 \<and> n \<noteq> 0"
  by (auto simp: intpow_def)


subsection \<open>Definitions\<close>

text\<open>
  The following function is a version of the p-adic valuation as defined in ~\cite{koblitz2012p}, 
  with the exception that for us the valuation of zero will be zero rather than infinity as in done
  in traditional mathematics. This definition is computational.
\<close>
definition pval :: \<open>nat \<Rightarrow> rat \<Rightarrow> int\<close> where
  \<open>pval p x = int (multiplicity p (fst (quotient_of x))) - 
              int (multiplicity p (snd (quotient_of x)))\<close>

text\<open>
  The following function is the p-adic norm as defined in ~\cite{koblitz2012p}.  This definition is
  computational.
\<close>
definition pnorm :: \<open>nat \<Rightarrow> rat \<Rightarrow> real\<close> where
  \<open>pnorm p x = (if x = 0 then 0 else p powr -of_int (pval p x))\<close>

subsection \<open>Trivial simplifications\<close>

lemma pval_eq_imp_norm_eq: \<open>pval p x = pval p y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> pnorm p x = pnorm p y\<close>
  by (simp add: pnorm_def)

lemma pval_0 [simp]: "pval p 0 = 0"
  and pval_1 [simp]: "pval p 1 = 0"
  by (simp_all add: pval_def)

lemma pnorm_0 [simp]: "pnorm p 0 = 0"
  and pnorm_1 [simp]: "prime p \<Longrightarrow> pnorm p 1 = 1"
  by (simp_all add: pnorm_def prime_gt_0_nat)

lemma pnorm_nonneg: "pnorm p x \<ge> 0"
  by (simp add: pnorm_def)

lemma pnorm_pos: "x \<noteq> 0 \<Longrightarrow> prime p \<Longrightarrow> pnorm p x > 0"
  by (auto simp: pnorm_def)

lemma pnorm_eq_0_iff [simp]: "pnorm p x = 0 \<longleftrightarrow> p = 0 \<or> x = 0"
  by (auto simp: pnorm_def)

lemma pnorm_le_iff:
  assumes "prime p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "pnorm p x \<le> pnorm p y \<longleftrightarrow> pval p x \<ge> pval p y"
  using assms prime_gt_1_nat[of p] by (simp add: pnorm_def)

lemma pnorm_less_iff:
  assumes "prime p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "pnorm p x < pnorm p y \<longleftrightarrow> pval p x > pval p y"
  using assms prime_gt_1_nat[of p] by (simp add: pnorm_def)

lemma pnorm_eq_iff:
  assumes "prime p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "pnorm p x = pnorm p y \<longleftrightarrow> pval p x = pval p y"
  using assms prime_gt_1_nat[of p] by (simp add: pnorm_def powr_inj)

lemma pnorm_eq_imp_pval_eq:
  assumes "pnorm p x = pnorm p y" "prime p"
  shows   "pval p x = pval p y"
  using assms prime_gt_1_nat[of p]
  by (cases "x = 0 \<or> y = 0") (auto simp: pnorm_def powr_inj split: if_splits)

(*
  Comment by Manuel:
  his lemma allows to determine a fraction's p-adic valuation even if it is not on
  lowest terms
*)
lemma pval_quotient:
  assumes "prime p" and [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "pval p (of_int a / of_int b) = int (multiplicity p a) - int (multiplicity p b)"
proof -
  define d where "d = sgn b * gcd a b"
  define a' b' where "a' = a div d" and "b' = b div d"
  have a'b': "a = a' * d" "b = b' * d"
    by (simp_all add: d_def a'_def b'_def)
  from assms have [simp]: "a' \<noteq> 0" "b' \<noteq> 0" "d \<noteq> 0"
    by (simp_all add: a'b')

  have "pval p (of_int a / of_int b) = int (multiplicity p a') - int (multiplicity p b')"
    by (auto simp: pval_def rat_divide_code case_prod_unfold Let_def
                   Rat.normalize_def d_def a'_def b'_def sgn_if)
  also have "\<dots> = int (multiplicity p a' + multiplicity p d) -
                  int (multiplicity p b' + multiplicity p d)" by simp
  also have "\<dots> = int (multiplicity p a) - int (multiplicity p b)"
    unfolding a'b' using \<open>prime p\<close>
    by (subst (1 2) prime_elem_multiplicity_mult_distrib) auto
  finally show ?thesis .
qed

lemma pval_of_int [simp]: "pval p (of_int n) = multiplicity p n"
  by (simp add: pval_def)

lemma pval_of_nat [simp]: "pval p (of_nat n) = multiplicity p n"
  using pval_of_int[of p "int n"] by (simp del: pval_of_int)

lemma pval_numeral [simp]: "pval p (numeral n) = multiplicity p (numeral n)"
  using pval_of_nat[of p "numeral n"] by (simp del: pval_of_nat)

lemma pval_mult [simp]:
  assumes "prime p" and [simp]: "x \<noteq> 0" "y \<noteq> 0"
  shows "pval p (x * y) = pval p x + pval p y"
proof -
  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  define c d where "c = fst (quotient_of y)" and "d = snd (quotient_of y)"
  have xy: "x = of_int a / of_int b" "y = of_int c / of_int d"
    by (rule quotient_of_div; simp add: a_def b_def c_def d_def)+
  have [simp]: "a \<noteq> 0" "c \<noteq> 0" using xy by auto
  have [simp]: "b \<noteq> 0" "d \<noteq> 0" by (auto simp: b_def d_def)

  have "x * y = of_int (a * c) / of_int (b * d)"
    by (simp add: xy)
  also have "pval p \<dots> = int (multiplicity p (a * c)) - int (multiplicity p (b * d))"
    using \<open>prime p\<close> by (subst pval_quotient) auto
  also have "\<dots> = pval p x + pval p y"
    using \<open>prime p\<close> by (simp add: xy pval_quotient prime_elem_multiplicity_mult_distrib)
  finally show ?thesis .
qed

lemma pnorm_mult [simp]: "prime p \<Longrightarrow> pnorm p (x * y) = pnorm p x * pnorm p y"
  by (simp add: pnorm_def powr_diff powr_minus field_simps)

lemma pval_inverse [simp]: "pval p (inverse x) = -pval p x"
proof (cases "x = 0")
  case [simp]: False
  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  have x: "x = of_int a / of_int b"
    by (rule quotient_of_div; simp add: a_def b_def)
  have [simp]: "a \<noteq> 0" using x by auto
  have [simp]: "b \<noteq> 0" by (auto simp: b_def)

  have "\<bar>a\<bar> = sgn a * a"  by (simp add: abs_if sgn_if)
  thus ?thesis
    by (auto simp: pval_def rat_inverse_code case_prod_unfold Let_def 
                   multiplicity_times_unit_right simp flip: a_def b_def)
qed auto

lemma pnorm_inverse [simp]: "pnorm p (inverse x) = inverse (pnorm p x)"
  by (simp add: pnorm_def powr_minus)

lemma pval_minus [simp]: "pval p (-x) = pval p x"
  by (simp add: pval_def rat_uminus_code case_prod_unfold Let_def)

lemma pnorm_minus [simp]: "pnorm p (-x) = pnorm p x"
  by (simp add: pnorm_def)

lemma pval_power [simp]:
  assumes "prime p"
  shows   "pval p (x ^ n) = int n * pval p x"
proof (cases "x = 0")
  case False
  thus ?thesis by (induction n) (auto simp: \<open>prime p\<close> algebra_simps)
qed (auto simp: power_0_left)

lemma pnorm_power [simp]: "prime p \<Longrightarrow> pnorm p (x ^ n) = pnorm p x ^ n"
  by (auto simp: pnorm_def powr_def simp flip: exp_of_nat_mult)

lemma pval_primepow: \<open>prime p \<Longrightarrow> pval p (of_int p ^ l) = l\<close>
  by simp

lemma pnorm_primepow: \<open>prime p \<Longrightarrow> pnorm p ((of_int p)^l) = 1/p^l\<close>
  using prime_gt_1_nat[of p]
  by (simp add: pval_primepow pnorm_def powr_minus powr_realpow field_simps)

lemma pval_eq_0_imp_pnorm_eq_1: "prime p \<Longrightarrow> pval p x = 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> pnorm p x = 1"
  by (auto simp: pnorm_def)

lemma pnorm_eq_1_imp_pval_eq_0: "prime p \<Longrightarrow> pnorm p x = 1 \<Longrightarrow> pval p x = 0"
  using pnorm_eq_iff[of p x 1] by (cases "x = 0") auto

lemma pnorm_eq_1_iff: "x \<noteq> 0 \<Longrightarrow> prime p \<Longrightarrow> pnorm p x = 1 \<longleftrightarrow> pval p x = 0"
  using pval_eq_0_imp_pnorm_eq_1 pnorm_eq_1_imp_pval_eq_0 by metis

lemma pval_coprime_quotient_cases:
  fixes a b :: int
  assumes "prime p" "coprime a b" and [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "\<not>p dvd b \<and> pval p (of_int a / of_int b) = int (multiplicity p a) \<or>
           \<not>p dvd a \<and> pval p (of_int a / of_int b) = -int (multiplicity p b)"
proof -
  have "\<not>p dvd a \<or> \<not>p dvd b"
    using assms by (meson coprime_common_divisor not_prime_unit prime_nat_int_transfer)
  thus ?thesis using \<open>prime p\<close>
    by (auto simp: pval_quotient not_dvd_imp_multiplicity_0)
qed

lemma pval_cases:
  fixes a b :: int
  assumes "prime p" "x \<noteq> 0"
  shows   "\<not>p dvd snd (quotient_of x) \<and> pval p x = int (multiplicity p (fst (quotient_of x))) \<or>
           \<not>p dvd fst (quotient_of x) \<and> pval p x = -int (multiplicity p (snd (quotient_of x)))"
proof -
  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  have x: "x = of_int a / of_int b"
    by (rule quotient_of_div) (simp add: a_def b_def)
  have [simp]: "a \<noteq> 0" using assms by (simp add: x)
  have [simp]: "b \<noteq> 0" by (simp add: b_def)
  have "coprime a b"
    by (rule quotient_of_coprime) (auto simp: a_def b_def)  
  thus "\<not>p dvd b \<and> pval p x = int (multiplicity p a) \<or>
           \<not>p dvd a \<and> pval p x = -int (multiplicity p b)"
    using pval_coprime_quotient_cases[of p a b] x[symmetric] assms by simp
qed


subsection \<open>Integers\<close>

lemma pval_nonneg_imp_in_Ints:
  assumes "\<And>p. prime p \<Longrightarrow> pval p x \<ge> 0"
  shows   "x \<in> \<int>"
proof (cases "x = 0")
  case False
  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  have x: "x = of_int a / of_int b"
    by (rule quotient_of_div) (simp add: a_def b_def)
  have [simp]: "a \<noteq> 0" using False by (simp add: x)
  have [simp]: "b \<noteq> 0" by (simp add: b_def)
  have "coprime a b"
    by (rule quotient_of_coprime) (auto simp: a_def b_def)

  hence *: "multiplicity p b = 0" if "prime p" for p :: nat
    using assms[of p] pval_coprime_quotient_cases[of p a b] that by (auto simp: x pval_quotient)
  have "multiplicity p b = 0" if "prime p" for p :: int
  proof -
    have "multiplicity (int (nat p)) b = 0"
      by (rule *) (use that in auto)
    thus ?thesis using prime_ge_0_int[of p] that by simp
  qed
  hence "prime_factors b = {}"
    by (auto simp: prime_factors_multiplicity)
  hence "is_unit b"
    using \<open>b \<noteq> 0\<close> prime_factorization_empty_iff by blast
  hence [simp]: "b = 1"
    using quotient_of_denom_pos[of x a b] by (simp add: a_def b_def)
  thus ?thesis by (simp add: x)
qed auto

lemma pval_Ints_nonneg: \<open>x \<in> \<int> \<Longrightarrow> prime p \<Longrightarrow> pval p x \<ge> 0\<close>
  by (auto elim: Ints_cases)

lemma in_Ints_iff_pval_nonneg: \<open>x \<in> \<int> \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> pval p x \<ge> 0)\<close>
  using pval_nonneg_imp_in_Ints pval_Ints_nonneg by blast 

lemma pnorm_le_1_imp_in_Ints: \<open>(\<And>p. prime p \<Longrightarrow> pnorm p x \<le> 1) \<Longrightarrow> x \<in> \<int>\<close>
  using pnorm_le_iff[of _ x 1] in_Ints_iff_pval_nonneg[of x]
  by (cases "x = 0") auto

lemma in_Ints_imp_pnorm_le_1:
  \<open>x \<in> \<int> \<Longrightarrow> prime p \<Longrightarrow> pnorm p x \<le> 1\<close>
  using pnorm_le_iff[of _ x 1] in_Ints_iff_pval_nonneg[of x]
  by (cases "x = 0") auto

lemma integers_pnorm:
  \<open>x \<in> \<int> \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> pnorm p x \<le> 1)\<close>
  using pnorm_le_1_imp_in_Ints in_Ints_imp_pnorm_le_1 by blast


subsection \<open>Divisibility of the numerator and the denominator\<close>

lemma pval_nonneg_iff:
  assumes "prime p" "x \<noteq> 0"
  shows   "pval p x \<ge> 0 \<longleftrightarrow> \<not>p dvd snd (quotient_of x)"
  using pval_cases[of p x] assms by (auto simp: prime_elem_multiplicity_eq_zero_iff)

lemma pval_nonpos_iff:
  assumes "prime p" "x \<noteq> 0"
  shows   "pval p x \<le> 0 \<longleftrightarrow> \<not>p dvd fst (quotient_of x)"
  using pval_cases[of p x] assms by (auto simp: prime_elem_multiplicity_eq_zero_iff)

lemma pval_neg_iff:
  assumes "prime p" "x \<noteq> 0"
  shows   "pval p x < 0 \<longleftrightarrow> p dvd snd (quotient_of x)"
  using pval_cases[of p x] assms by (auto simp: prime_multiplicity_gt_zero_iff)

lemma pval_pos_iff:
  assumes "prime p" "x \<noteq> 0"
  shows   "pval p x > 0 \<longleftrightarrow> p dvd fst (quotient_of x)"
  using pval_cases[of p x] assms by (auto simp: prime_multiplicity_gt_zero_iff)

lemma pval_eq_0_iff:
  assumes "prime p" "x \<noteq> 0"
  shows   "pval p x = 0 \<longleftrightarrow> \<not>p dvd fst (quotient_of x) \<and> \<not>p dvd snd (quotient_of x)"
  using pval_cases[of p x] assms
  by (auto simp: not_dvd_imp_multiplicity_0 prime_elem_multiplicity_eq_zero_iff)


subsection \<open>Existence and uniqueness of decomposition\<close>

(*
  Comment by Manuel:
  It's really not a good idea to work with the real or complex power operation here.
  What one really needs here is an integer power operation
*)

lemma pval_intpow [simp]: "prime p \<Longrightarrow> pval p (intpow x n) = n * pval p x"
  by (auto simp: intpow_def)

lemma pval_decomposition_exists:
  assumes "prime p"
  shows   "\<exists>y. x = intpow (of_nat p) (pval p x) * y \<and> pval p y = 0"
proof (cases "x = 0")
  case [simp]: False
  define y where "y = x / intpow (of_nat p) (pval p x)"
  from assms have [simp]: "y \<noteq> 0" by (auto simp: y_def)
  from assms have eq: "x = intpow (of_nat p) (pval p x) * y"
    by (auto simp: y_def)
  have "pval p x = pval p (intpow (of_nat p) (pval p x) * y)"
    by (subst eq) auto
  hence "pval p y = 0" using assms by simp
  with eq show ?thesis by blast
qed auto

lemma pval_decomposition_unique:
  fixes p :: nat and x y :: rat and l :: int
  shows \<open>prime p \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x = intpow (of_int p) l * y \<Longrightarrow> pval p y = 0 \<Longrightarrow> pval p x = l\<close>
  by auto

(*
  Comment by Manuel:
  This is essentially just a copy of the above. Since pnorm = 1 iff pval = 0, there is really
  no point in stating this again.
*)
lemma pnorm_decomposition:
  \<open>prime p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> \<exists> y::rat. (x::rat) = (p powr (pval p x)) * y \<and> pnorm p y = 1\<close>
  oops

subsection \<open>Unit ball\<close>

(* 
  Comment by Manuel: This is the generalised version of your unit ball properties.
  pval (x + y) is greater than or equal to the minimum of the pvals of x and y, with equality
  holding if x and y have distinct pvals.
*)

lemma pval_add_ge:
  assumes "prime p"
  assumes "x + y \<noteq> 0"
  shows "pval p (x + y) \<ge> min (pval p x) (pval p y)"
proof (cases "x = 0 \<or> y = 0")
  case False
  hence [simp]: "x \<noteq> 0" "y \<noteq> 0" by auto
  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  define c d where "c = fst (quotient_of y)" and "d = snd (quotient_of y)"
  have xy: "x = of_int a / of_int b" "y = of_int c / of_int d"
    by (rule quotient_of_div; simp add: a_def b_def c_def d_def)+
  have [simp]: "a \<noteq> 0" "c \<noteq> 0" using xy by auto
  have [simp]: "b \<noteq> 0" "d \<noteq> 0" by (auto simp: b_def d_def)
  have eq: "x + y = of_int (a * d + b * c) / of_int (b * d)"
    by (simp add: xy field_simps)

  have nz: "a * d + b * c \<noteq> 0"
  proof
    assume *: "a * d + b * c = 0"
    have "x + y = 0"
      unfolding eq * by simp
    with assms show False by simp
  qed

  have "min (pval p x) (pval p y) = 
          int (min (multiplicity (int p) (a * d)) (multiplicity (int p) (b * c))) -
          int (multiplicity (int p) (b * d))" using \<open>prime p\<close>
    by (simp add: xy pval_quotient prime_elem_multiplicity_mult_distrib)
  also have "\<dots> \<le> int (multiplicity (int p) (a * d + b * c)) - int (multiplicity (int p) (b * d))"
    using multiplicity_add_ge[of "a * d" "b * c" p] nz
    by (intro diff_right_mono) auto
  also have "\<dots> = pval p (x + y)"
    using nz assms by (subst eq, subst pval_quotient) auto
  finally show ?thesis .
qed auto

lemma pval_diff_ge:
  assumes "prime p"
  assumes "x \<noteq> y"
  shows "pval p (x - y) \<ge> min (pval p x) (pval p y)"
  using pval_add_ge[of p x "-y"] assms by auto

lemma pnorm_add_le: "prime p \<Longrightarrow> pnorm p (x + y) \<le> max (pnorm p x) (pnorm p y)"
  using pval_add_ge[of p x y] prime_gt_1_nat[of p]
  by (cases "x + y = 0") (auto simp: pnorm_def max_def)

lemma pnorm_diff_le:  "prime p \<Longrightarrow> pnorm p (x - y) \<le> max (pnorm p x) (pnorm p y)"
  using pnorm_add_le[of p x "-y"] by simp

lemma pnorm_sum_le:
  fixes p::nat and A::\<open>nat set\<close> and x::\<open>nat \<Rightarrow> rat\<close>
  assumes "finite A" "A \<noteq> {}" \<open>prime p\<close>
  shows "pnorm p (sum x A) \<le> Max ((\<lambda> i. pnorm p (x i)) ` A)"
  using assms
proof (induction rule: finite_ne_induct)
  case (singleton y)
  thus ?case by auto
next
  case (insert y A)
  have "pnorm p (x y + sum x A) \<le> max (pnorm p (x y)) (pnorm p (sum x A))"
    by (rule pnorm_add_le) fact
  also have "\<dots> \<le> max (pnorm p (x y)) (MAX i\<in>A. pnorm p (x i))"
    by (intro max.mono insert.IH) (auto simp: \<open>prime p\<close>)
  finally show ?case
    using insert.hyps by simp
qed

lemma pval_add_absorb_left [simp]:
  assumes "prime p" "x \<noteq> 0" "pval p x < pval p y"
  shows   "pval p (x + y) = pval p x"
proof (cases "y = 0")
  case False
  with assms have [simp]: "x \<noteq> 0" "y \<noteq> 0" by auto
  from assms have "x \<noteq> -y" by auto
  hence "x + y \<noteq> 0" by linarith

  define a b where "a = fst (quotient_of x)" and "b = snd (quotient_of x)"
  define c d where "c = fst (quotient_of y)" and "d = snd (quotient_of y)"
  have xy: "x = of_int a / of_int b" "y = of_int c / of_int d"
    by (rule quotient_of_div; simp add: a_def b_def c_def d_def)+
  have [simp]: "a \<noteq> 0" "c \<noteq> 0" using xy by auto
  have [simp]: "b \<noteq> 0" "d \<noteq> 0" by (auto simp: b_def d_def)
  have eq: "x + y = of_int (a * d + b * c) / of_int (b * d)"
    by (simp add: xy field_simps)

  have nz: "a * d + b * c \<noteq> 0"
  proof
    assume *: "a * d + b * c = 0"
    have "x + y = 0"
      unfolding eq * by simp
    with \<open>x + y \<noteq> 0\<close> show False by simp
  qed

  have "pval p (x + y) = int (multiplicity (int p) (a * d + b * c)) - 
          int (multiplicity (int p) (b * d))"
    using nz assms by (subst eq, subst pval_quotient) auto
  also from assms have "multiplicity (int p) (a * d) < multiplicity (int p) (b * c)"
    by (auto simp: pval_quotient xy prime_elem_multiplicity_mult_distrib)
  hence "multiplicity (int p) (a * d + b * c) = multiplicity (int p) (a * d)"
    by (rule multiplicity_add_absorb_left) auto
  also have "\<dots> - int (multiplicity (int p) (b * d)) = pval p x"
    using assms by (simp add: xy pval_quotient prime_elem_multiplicity_mult_distrib)
  finally show "pval p (x + y) = pval p x" .
qed (use assms in auto)

lemma pval_add_absorb_right [simp]:
  assumes "prime p" "y \<noteq> 0" "pval p y < pval p x"
  shows   "pval p (x + y) = pval p y"
  using pval_add_absorb_left[of p y x] assms by (simp add: add.commute del: pval_add_absorb_left)

lemma pnorm_add_absorb_left [simp]:
  assumes "prime p" "x \<noteq> 0" "pnorm p x > pnorm p y"
  shows   "pnorm p (x + y) = pnorm p x"
proof (cases "y = 0")
  case False
  with assms have [simp]: "x \<noteq> 0" "y \<noteq> 0" by auto
  from assms have "x \<noteq> -y" by auto
  hence [simp]: "x + y \<noteq> 0" by linarith
  have "pval p (x + y) = pval p x"
    using assms by (intro pval_add_absorb_left) (auto simp: pnorm_less_iff)
  thus ?thesis by (simp add: pnorm_def)
qed (use assms in auto)

lemma pnorm_add_absorb_right [simp]:
  assumes "prime p" "y \<noteq> 0" "pnorm p x < pnorm p y"
  shows   "pnorm p (x + y) = pnorm p y"
  using pnorm_add_absorb_left[of p y x] assms by (simp add: add.commute del: pnorm_add_absorb_left)

(* Comment by Manuel: this is now a simple corollary *)
lemma pnorm_unit_ball:
  fixes n :: nat
  assumes \<open>prime p\<close> and \<open>pnorm p x = 1\<close> and \<open>pnorm p y < 1\<close>
  shows \<open>pnorm p (x + y) = 1\<close>
  using assms by (subst pnorm_add_absorb_left) auto

end