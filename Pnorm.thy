(*
  File:    Pnorm.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>p-adic valuation and p-adic norm\<close>
theory Pnorm

imports 
  "Probabilistic_Prime_Tests.Fermat_Witness"

begin

text \<open>
  Following ~\cite{koblitz2012p}, we define the p-adic valuation @{text pval}, the p-adic norm 
  @{text pnorm} in a computational way. We prove their basic properties.
\<close>

subsection \<open>Unsorted\<close>

(* The lemmas from this section are preliminaries which does not represent the aim of this library. 
   Hence, they can be moved to the better place. *)

lemma quotient_of_dvd_or:
  \<open>\<not> is_unit p \<Longrightarrow> \<not> ( p dvd (fst (quotient_of x)) ) \<or> \<not> ( p dvd (snd (quotient_of x)) )\<close>
proof-
  assume \<open>\<not> is_unit p\<close>
  show ?thesis
  proof(rule classical)
    assume \<open>\<not>(\<not> ( p dvd (fst (quotient_of x)) ) \<or>  \<not> ( p dvd (snd (quotient_of x)) ))\<close>
    hence \<open>p dvd (fst (quotient_of x)) \<and> p dvd (snd (quotient_of x))\<close>
      by blast
    hence \<open>\<not> coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
      using \<open>\<not> is_unit p\<close> coprime_common_divisor not_prime_unit 
      by blast
    thus ?thesis
      using quotient_of_coprime 
      by auto 
  qed
qed

lemma fst_quotient_of_divide:
  \<open>n \<noteq> 0 \<Longrightarrow> fst (quotient_of (Fract m n)) dvd m\<close>
proof-
  assume \<open>n \<noteq> 0\<close>
  have \<open>snd (quotient_of (Fract m n)) \<noteq> 0\<close>
    by (smt quotient_of_denom_pos')
  have \<open>fst (quotient_of (Fract m n))/snd (quotient_of (Fract m n)) = Fract m n\<close>
    by (metis (mono_tags, hide_lams) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
        prod.exhaust_sel quotient_of_div)
  hence \<open>fst (quotient_of (Fract m n))*n = m*snd (quotient_of (Fract m n))\<close>
    using \<open>n \<noteq> 0\<close> \<open>snd (quotient_of (Fract m n)) \<noteq> 0\<close> 
      frac_eq_eq[where z = n and y = "snd (quotient_of (Fract m n))" and w = "m" 
        and x = "fst (quotient_of (Fract m n))"]
    by (metis (no_types, lifting) of_int_0_eq_iff of_int_eq_iff of_int_mult of_rat_rat
        prod.collapse quotient_of_eq) 
  hence \<open>fst (quotient_of (Fract m n)) dvd (m*snd (quotient_of (Fract m n)))\<close>
    by (metis dvdI)
  moreover have \<open>coprime (fst (quotient_of (Fract m n))) (snd (quotient_of (Fract m n)))\<close>
    using Rat.quotient_of_coprime
    by simp
  ultimately show ?thesis
    using coprime_dvd_mult_left_iff 
    by blast 
qed

lemma snd_quotient_of_divide:
  \<open>snd (quotient_of (Fract m n)) dvd n\<close>
proof(cases \<open>n = 0\<close>)
  case True
  thus ?thesis 
    by auto
next
  case False
  have \<open>snd (quotient_of (Fract m n)) \<noteq> 0\<close>
    by (smt quotient_of_denom_pos')
  have \<open>fst (quotient_of (Fract m n))/snd (quotient_of (Fract m n)) = Fract m n\<close>
    by (metis (mono_tags, hide_lams) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
        prod.exhaust_sel quotient_of_div)
  hence \<open>fst (quotient_of (Fract m n))*n = m*snd (quotient_of (Fract m n))\<close>
    using \<open>n \<noteq> 0\<close> \<open>snd (quotient_of (Fract m n)) \<noteq> 0\<close> 
      frac_eq_eq[where z = n and y = "snd (quotient_of (Fract m n))" and w = "m" 
        and x = "fst (quotient_of (Fract m n))"]
    by (metis (no_types, lifting) of_int_0_eq_iff of_int_eq_iff of_int_mult of_rat_rat
        prod.collapse quotient_of_eq) 
  hence \<open>snd (quotient_of (Fract m n)) dvd (fst (quotient_of (Fract m n))*n)\<close>
    by simp    
  moreover have \<open>coprime (fst (quotient_of (Fract m n))) (snd (quotient_of (Fract m n)))\<close>
    using Rat.quotient_of_coprime
    by simp
  ultimately show ?thesis
    using coprime_commute coprime_dvd_mult_right_iff 
    by blast
qed

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
  \<open>pnorm p x = (if x = 0 
  then 0
  else  p powr  (int (multiplicity p  (snd (quotient_of x)) )
               - int (multiplicity p  (fst (quotient_of x)) )) 
) \<close>

subsection \<open>Trivial simplifications\<close>

lemma pnorm_simplified:
  \<open>x \<noteq> 0 \<Longrightarrow> pnorm p x = p powr  (- (pval p x) )\<close>
  unfolding pval_def pnorm_def
  by auto

lemma pval_pnorm: \<open>pval p x = pval p y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> pnorm p x = pnorm p y\<close>
  using pnorm_simplified
  by auto

lemma pnorm_pval: \<open>prime p \<Longrightarrow> pnorm p x = pnorm p y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> pval p x = pval p y\<close>
proof-
  assume \<open>prime p\<close> and \<open>pnorm p x = pnorm p y\<close> and \<open>x \<noteq> 0\<close> and \<open>y \<noteq> 0\<close>
  have \<open>pnorm p x = p powr (- pval p x)\<close>
    using pnorm_simplified[where p = p and x = x] \<open>x \<noteq> 0\<close>
    by simp
  moreover have \<open>pnorm p y = p powr (- pval p y)\<close>
    using pnorm_simplified[where p = p and x = y] \<open>y \<noteq> 0\<close>
    by simp
  ultimately have \<open>p powr (- pval p x) = p powr (- pval p y)\<close>
    using \<open>pnorm p x = pnorm p y\<close>
    by simp
  moreover have \<open>p > 1\<close>
    using \<open>prime p\<close> prime_nat_iff 
    by blast
  ultimately have \<open>- pval p x = - pval p y\<close>
    by (simp add: powr_inj)
  thus ?thesis
    by auto
qed  

lemma pval_zero: \<open>pval p 0 = 0\<close>
proof-
  have \<open>quotient_of 0 = (0, 1)\<close>
    by simp
  thus ?thesis
    unfolding pval_def
    by auto
qed

lemma pnorm_1:
  \<open>pnorm 2 1 = 1\<close>
proof-
  have \<open>pval 2 1 = 0\<close>
    unfolding pval_def
    by auto
  thus ?thesis
    unfolding pnorm_def
    by auto
qed

lemma pval_primepow:
  \<open>prime p \<Longrightarrow> pval p ((of_int p)^l) = l\<close>
proof-
  assume \<open>prime p\<close>
  define x where \<open>x = Fract (p^l) 1\<close>
  have \<open>quotient_of x = (p^l, 1)\<close>
  proof-
    have \<open>coprime (p^l) 1\<close>
      by simp      
    thus ?thesis 
      unfolding x_def
      by (simp add: quotient_of_Fract)      
  qed
  have \<open>int (multiplicity p (fst (quotient_of x)) ) = l\<close>
  proof-
    have \<open>fst (quotient_of x) = p^l\<close>
      by (simp add: \<open>quotient_of x = (case (p ^ l, 1) of (x, y) \<Rightarrow> (int x, y))\<close>)
    thus ?thesis 
      by (simp add: \<open>prime p\<close>)
  qed
  moreover have \<open>int (multiplicity p  (snd (quotient_of x)) ) = 0\<close>
  proof-
    have \<open>snd (quotient_of x) = 1\<close>
      by (simp add: \<open>quotient_of x = (case (p ^ l, 1) of (x, y) \<Rightarrow> (int x, y))\<close>)
    thus ?thesis 
      by (simp add: \<open>prime p\<close>)
  qed
  moreover have \<open>x = (of_int p)^l\<close>
    by (metis Fract_of_nat_eq of_int_of_nat_eq of_nat_power x_def)    
  ultimately show ?thesis 
    unfolding pval_def
    by simp
qed

lemma pnorm_primepow:
  \<open>prime p \<Longrightarrow> pnorm p ((of_int p)^l) = 1/p^l\<close>
proof-
  assume \<open>prime p\<close>
  moreover have \<open>(of_int p)^l \<noteq> (0::rat)\<close>
    using calculation by auto
  ultimately have \<open>pnorm p ((of_int p)^l) = p powr  (- (pval p ((of_int p)^l)) )\<close>
    using pnorm_simplified 
    by auto
  moreover have \<open>pval p ((of_int p)^l) = l\<close>
    using pval_primepow \<open>prime p\<close>
    by auto
  ultimately have \<open>pnorm p ((of_int p)^l) = p powr (-l)\<close>
    by simp
  also have \<open>p powr (-l) = 1/p^l\<close>
    using Transcendental.powr_minus_divide[where x = "p" and a = "l"]
    by (simp add: \<open>prime p\<close> powr_realpow prime_gt_0_nat)
  finally show ?thesis 
    by simp
qed

lemma pval_integer:
  \<open>prime p \<Longrightarrow> pval p (Fract k 1) = multiplicity p k\<close>
proof-
  assume \<open>prime p\<close>
  have \<open>pval p (Fract k 1) = int (multiplicity p (fst (quotient_of (Fract k 1)))) -
    int (multiplicity p (snd (quotient_of (Fract k 1))))\<close>
    unfolding pval_def
    by blast
  moreover have \<open>int (multiplicity p (snd (quotient_of (Fract k 1)))) = 0\<close>
  proof-
    have \<open>snd (quotient_of (Fract k 1)) = 1\<close>
      using Fract_of_int_eq Rat.of_int_def quotient_of_int 
      by auto
    moreover have \<open>multiplicity p 1 = 0\<close>
      by simp
    ultimately show ?thesis 
      by auto
  qed
  moreover have \<open>int (multiplicity p (fst (quotient_of (Fract k 1)))) = multiplicity p k\<close>
  proof-
    have \<open>fst (quotient_of (Fract k 1)) = k\<close>
      using Fract_of_int_eq Rat.of_int_def quotient_of_int 
      by auto      
    thus ?thesis
      by simp 
  qed
  ultimately show ?thesis
    by auto
qed

lemma pnorm_geq_zero:
  assumes \<open>prime p\<close>
  shows \<open>pnorm p x \<ge> 0\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis 
    unfolding pnorm_def
    by auto
next
  case False
  thus ?thesis
    unfolding pnorm_def
    by auto
qed

lemma pnorm_eq_zero_D:
  \<open>prime p \<Longrightarrow> x = 0 \<Longrightarrow> pnorm p x = 0\<close>
  unfolding pnorm_def 
  by auto

lemma pnorm_eq_zero_I:
  \<open>prime p \<Longrightarrow> pnorm p x = 0 \<Longrightarrow> x = 0\<close>
  unfolding pnorm_def
  by (metis not_prime_0 of_nat_0_eq_iff powr_eq_0_iff)

lemma pnorm_eq_zero:
  assumes \<open>prime p\<close>
  shows \<open>pnorm p x = 0 \<longleftrightarrow> x = 0\<close>
  using assms pnorm_eq_zero_D pnorm_eq_zero_I 
  by blast

lemma pnorm_pval_zero_I:
  assumes \<open>prime p\<close> and \<open>pval p x = 0\<close> and \<open>x \<noteq> 0\<close>
  shows \<open>pnorm p x = 1\<close>
proof-
  have \<open>pnorm p x = p powr (-pval p x)\<close>
    by (simp add: assms(3) pnorm_simplified)
  also have \<open>\<dots> = 1\<close>
    by (simp add: assms(1) assms(2) prime_gt_0_nat)
  finally show ?thesis
    by simp
qed

lemma pnorm_pval_zero_D:
  assumes \<open>prime p\<close> and \<open>pnorm p x = 1\<close>
  shows \<open>pval p x = 0\<close> 
proof-
  have \<open>x \<noteq> 0\<close>
    using pnorm_eq_zero \<open>pnorm p x = 1\<close>
  proof -
    have "(0::real) \<noteq> 1"
      by auto
    thus ?thesis
      by (metis assms(1) assms(2) pnorm_eq_zero)
  qed
  hence \<open>p powr (-pval p x) = 1\<close>
    using assms(2) pnorm_simplified 
    by auto
  moreover have \<open>p > 0\<close>
    by (simp add: assms(1) prime_gt_0_nat)
  ultimately have \<open>-pval p x = 0\<close>
    by (metis (mono_tags) assms(1) less_irrefl_nat of_int_0_eq_iff of_nat_0 of_nat_1 of_nat_less_iff
        powr_inj powr_zero_eq_one prime_gt_1_nat)    
  thus ?thesis
    by simp    
qed

lemma pnorm_pval_zero:
  assumes \<open>x \<noteq> 0\<close> and \<open>prime p\<close>
  shows \<open>pnorm p x = 1 \<longleftrightarrow> pval p x = 0\<close>
  using assms(1) assms(2) pnorm_pval_zero_D pnorm_pval_zero_I 
  by blast

lemma pnorm_pval_g_zero_I:
  assumes \<open>prime p\<close> and \<open>pval p x > 0\<close> and \<open>x \<noteq> 0\<close>
  shows \<open>pnorm p x < 1\<close>
proof-
  have \<open>pnorm p x = p powr (-pval p x)\<close>
    by (simp add: assms(3) pnorm_simplified)
  also have \<open>\<dots> < 1\<close>
    by (metis (no_types) add.inverse_neutral assms(1) assms(2) less_numeral_extra(1) 
        neg_less_iff_less of_int_0_less_iff of_int_minus of_nat_1 of_nat_less_iff 
        powr_less_mono2_neg powr_one_eq_one prime_gt_1_nat)
  finally show ?thesis
    by simp
qed

lemma pnorm_pval_g_zero_D:
  assumes \<open>prime p\<close> \<open>pnorm p x < 1\<close> and \<open>x \<noteq> 0\<close>
  shows \<open>pval p x > 0\<close> 
proof-
  have \<open>p powr (-pval p x) < 1\<close>
    using \<open>pnorm p x < 1\<close> \<open>x \<noteq> 0\<close>
    by (simp add: pnorm_simplified)    
  moreover have \<open>p > 0\<close>
    by (simp add: assms(1) prime_gt_0_nat)
  ultimately have \<open>-pval p x < 0\<close>
    by (metis (mono_tags, hide_lams) less_irrefl_nat less_one linorder_neqE_nat of_int_less_0_iff 
        of_nat_0_less_iff of_nat_1 of_nat_eq_0_iff of_nat_less_iff powr_less_cancel_iff 
        powr_one_eq_one powr_zero_eq_one)
  thus ?thesis
    by simp    
qed

subsection \<open>Integers\<close>

lemma integers_pval_I:
  \<open>(\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0) \<Longrightarrow> x \<in> \<int>\<close>
proof-
  assume \<open>\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0\<close>
  have \<open>prime p \<Longrightarrow> multiplicity p (snd (quotient_of x)) = 0\<close>
    for p::nat
  proof-
    assume \<open>prime p\<close>
    hence \<open>pval p x \<ge> 0\<close>
      by (simp add: \<open>\<And>p. prime p \<Longrightarrow> 0 \<le> pval p x\<close>)
    hence \<open>multiplicity p (fst (quotient_of x)) \<ge> multiplicity p (snd (quotient_of x))\<close>
      using pval_def 
      by auto
    show ?thesis
    proof(rule classical)
      assume \<open>\<not>(multiplicity p (snd (quotient_of x)) = 0)\<close>
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        by simp
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity p (fst (quotient_of x)) \<ge> multiplicity p (snd (quotient_of x))\<close>
        by auto
      hence \<open>p dvd fst (quotient_of x)\<close>
        using not_dvd_imp_multiplicity_0 
        by fastforce
      moreover have \<open>p dvd snd (quotient_of x)\<close>
        by (meson \<open>multiplicity p (snd (quotient_of x)) \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      ultimately have \<open>\<not> coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
        by (meson \<open>multiplicity p (snd (quotient_of x)) \<noteq> 0\<close> coprime_common_divisor 
            multiplicity_unit_left)
      moreover have \<open>coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
        by (simp add: quotient_of_coprime)
      ultimately show ?thesis 
        by blast
    qed        
  qed
  moreover have \<open>prime p \<Longrightarrow> multiplicity p (1::nat) = 0\<close>
    for p::nat
    by simp    
  ultimately have \<open>snd (quotient_of x) = 1\<close>
    using multiplicity_eq_nat[where x = "nat (snd (quotient_of x))" and y = "(1::nat)" ]
    by (metis (full_types) less_irrefl_nat multiplicity_eq_int multiplicity_one not_prime_0
        prime_nat_iff_prime quotient_of_denom_pos' split_nat zero_less_one)    
  thus ?thesis
    by (metis Ints_of_int Rat.of_int_def eq_snd_iff quotient_of_inject quotient_of_int) 
qed

lemma integers_pval_D:
  \<open>x \<in> \<int> \<Longrightarrow> (\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0)\<close>
proof-
  fix x::rat
  assume \<open>x \<in> \<int>\<close>
  show \<open>prime p \<Longrightarrow> pval p x \<ge> 0\<close> 
    for p
  proof-
    assume \<open>prime p\<close>
    have \<open>snd (quotient_of x) = 1\<close>
      using  \<open>x \<in> \<int>\<close>
      by (metis Ints_cases Rat.of_int_def quotient_of_int sndI)      
    hence \<open>multiplicity p  (snd (quotient_of x)) = 0\<close>
      by auto
    thus ?thesis
      unfolding pval_def
      by simp
  qed
qed

lemma integers_pval:
  \<open>x \<in> \<int> \<longleftrightarrow> (\<forall> p. prime p \<longrightarrow> pval p x \<ge> 0)\<close>
  using integers_pval_D integers_pval_I 
  by blast 

lemma integers_pnorm_I:
  \<open>(\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1) \<Longrightarrow> x \<in> \<int>\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis by auto
next
  case False
  assume \<open>\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1\<close>
  have \<open>prime p \<Longrightarrow> pval p x \<ge> 0\<close>
    for p
  proof-
    assume \<open>prime p\<close>
    hence \<open>pnorm p x \<le> 1\<close>
      using \<open>\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1\<close>
      by blast
    moreover have \<open>pnorm p x = p powr (- (pval p x))\<close>
      by (simp add: False pnorm_simplified)      
    ultimately have \<open> p powr (- (pval p x)) \<le> 1\<close>
      by simp
    moreover have \<open>p > 1\<close>
      using \<open>prime p\<close> prime_nat_iff 
      by blast      
    ultimately show \<open>pval p x \<ge> 0\<close>
      by (metis add.inverse_inverse neg_0_le_iff_le of_int_0_le_iff of_int_minus of_nat_1 
          of_nat_less_0_iff of_nat_less_iff powr_le_cancel_iff powr_zero_eq_one)      
  qed
  thus ?thesis
    using integers_pval_I by blast 
qed

lemma integers_pnorm_D:
  \<open>x \<in> \<int> \<Longrightarrow> (\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1)\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus \<open>prime p \<Longrightarrow> pnorm p x \<le> 1\<close> 
    for p 
  proof-
    assume \<open>prime p\<close>
    have \<open>pnorm p x = 0\<close>
      unfolding pnorm_def
      using True
      by auto
    thus ?thesis by auto
  qed
next
  case False
  assume \<open>x \<in> \<int>\<close>
  show \<open>prime p \<Longrightarrow> pnorm p x \<le> 1\<close> 
    for p
  proof-
    assume \<open>prime p\<close>
    hence \<open>pval p x \<ge> 0\<close>
      using  \<open>x \<in> \<int>\<close> integers_pval_D 
      by auto
    moreover have \<open>p > 1\<close>
      using \<open>prime p\<close> prime_nat_iff by blast
    moreover have \<open>pnorm p x = p powr (- (pval p x))\<close>
      using False
      by (simp add: pnorm_simplified) 
    ultimately show ?thesis
      by (metis less_one less_or_eq_imp_le negative_zle_0 of_int_le_0_iff of_nat_0_less_iff of_nat_1
          of_nat_le_iff powr_mono2' powr_one_eq_one zero_le_imp_eq_int)
  qed
qed

lemma integers_pnorm:
  \<open>x \<in> \<int> \<longleftrightarrow> (\<forall> p. prime p \<longrightarrow> pnorm p x \<le> 1)\<close>
  using integers_pnorm_D integers_pnorm_I 
  by blast

subsection \<open>Divisibility of the numerator and the denominator\<close>

lemma pval_unit_dvd_I:
  \<open>prime p \<Longrightarrow> x \<noteq> 0  \<Longrightarrow> pval p x = 0 
  \<Longrightarrow> \<not>(p dvd (fst (quotient_of x))) \<and> \<not>(p dvd (snd (quotient_of x)))\<close>
proof-
  assume \<open>prime p\<close> and \<open>x \<noteq> 0\<close> and \<open>pval p x = 0\<close>
  have \<open>pval p x = (multiplicity p (fst (quotient_of x))) - (multiplicity p (snd (quotient_of x)))\<close>
    using \<open>pval p x = 0\<close> pval_def 
    by auto
  hence \<open>(multiplicity p (fst (quotient_of x))) = (multiplicity p (snd (quotient_of x)))\<close>
    using \<open>pval p x = 0\<close>
    by (simp add: pval_def)
  show ?thesis
  proof(rule classical)
    assume \<open>\<not> (\<not>(p dvd (fst (quotient_of x))) \<and> \<not>(p dvd (snd (quotient_of x))))\<close>
    hence \<open>(p dvd (fst (quotient_of x))) \<or> (p dvd (snd (quotient_of x)))\<close>
      by blast
    have \<open>(p dvd (fst (quotient_of x))) \<and> (p dvd (snd (quotient_of x)))\<close>      
    proof(cases \<open>p dvd (fst (quotient_of x))\<close>)
      case True
      moreover have \<open>\<not> is_unit (int p)\<close>
        using \<open>prime p\<close> 
        by auto
      moreover have \<open>fst (quotient_of x) \<noteq> 0\<close>
      proof(rule classical)
        assume \<open>\<not> ( fst (quotient_of x) \<noteq> 0 )\<close>
        hence \<open>fst (quotient_of x) = 0\<close>
          by blast
        show ?thesis
          by (metis Fract_of_int_quotient Zero_rat_def \<open>x \<noteq> 0\<close>  eq_rat(3) prod.collapse 
              quotient_of_div)          
      qed
      ultimately have \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using multiplicity_geI[where n = 1 and p = p and x = "fst (quotient_of x)"]
        by simp
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity p (fst (quotient_of x)) = multiplicity p (snd (quotient_of x))\<close> 
        by linarith
      hence \<open>p dvd (snd (quotient_of x))\<close>
        using le_numeral_extra(2) not_dvd_imp_multiplicity_0 ord_le_eq_trans 
        by blast
      thus ?thesis
        by (simp add: True) 
    next
      case False
      hence \<open>p dvd (snd (quotient_of x))\<close>
        using \<open>int p dvd fst (quotient_of x) \<or> int p dvd snd (quotient_of x)\<close> 
        by auto
      moreover have \<open>\<not> is_unit (int p)\<close>
        using \<open>prime p\<close> 
        by auto
      moreover have \<open>snd (quotient_of x) \<noteq> 0\<close>
        by (metis less_int_code(1) quotient_of_denom_pos')      
      ultimately have \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        using multiplicity_geI[where n = 1 and p = p and x = "snd (quotient_of x)"]
        by simp
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity p (fst (quotient_of x)) = multiplicity p (snd (quotient_of x))\<close> 
        by linarith
      hence \<open>p dvd (fst (quotient_of x))\<close>
        using le_numeral_extra(2) not_dvd_imp_multiplicity_0 ord_le_eq_trans 
        by blast
      thus ?thesis
        by (simp add: False) 
    qed
    moreover have \<open>coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
      using Rat.quotient_of_coprime
      by simp
    ultimately show ?thesis
      by (meson \<open>prime p\<close> not_coprimeI not_prime_unit prime_nat_int_transfer)       
  qed
qed

lemma pval_unit_dvd_D:
  \<open>prime p \<Longrightarrow> x \<noteq> 0  \<Longrightarrow> \<not>(p dvd (fst (quotient_of x))) \<Longrightarrow> \<not>(p dvd (snd (quotient_of x))) 
  \<Longrightarrow> pval p x = 0\<close>
proof-
  assume \<open>prime p\<close> and \<open>x \<noteq> 0\<close> and \<open>\<not>(p dvd (fst (quotient_of x)))\<close> 
    and \<open>\<not>(p dvd (snd (quotient_of x)))\<close>
  have \<open>multiplicity p (fst (quotient_of x)) = 0\<close>
    using  \<open>\<not>(p dvd (fst (quotient_of x)))\<close>
    by (simp add: not_dvd_imp_multiplicity_0)
  moreover have \<open>multiplicity p (snd (quotient_of x)) = 0\<close>
    using  \<open>\<not>(p dvd (snd (quotient_of x)))\<close>
    by (simp add: not_dvd_imp_multiplicity_0)
  ultimately show ?thesis
    by (simp add: pval_def) 
qed

lemma pval_unit_dvd:
  \<open>prime p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 
  (\<not>(p dvd (fst (quotient_of x))) \<and> \<not>(p dvd (snd (quotient_of x)))) \<longleftrightarrow> pval p x = 0\<close>
  using pval_unit_dvd_D pval_unit_dvd_I 
  by blast

lemma pnorm_1_Fract:
  \<open>prime p \<Longrightarrow> pnorm p x = 1 \<Longrightarrow> \<not> (p dvd fst (quotient_of x)) \<and>  \<not> (p dvd snd (quotient_of x))\<close>
proof-
  assume \<open>prime p\<close> and \<open>pnorm p x = 1\<close>
  have \<open>x \<noteq> 0\<close>
  proof -
    have "(0::real) \<noteq> 1"
      by auto
    thus ?thesis
      by (metis (full_types) \<open>pnorm p x = 1\<close> \<open>prime p\<close> pnorm_eq_zero)
  qed
  thus ?thesis
    using pval_unit_dvd_I \<open>pnorm p x = 1\<close> \<open>prime p\<close> pnorm_pval_zero 
    by auto
qed

lemma pnorm_l_1_Fract:
  \<open>prime p \<Longrightarrow> pnorm p x < 1 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow>
   p dvd fst (quotient_of x) \<and> \<not> (p dvd snd (quotient_of x))\<close>
proof-
  assume \<open>prime p\<close> and \<open>pnorm p x < 1\<close> and \<open>x \<noteq> 0\<close>
  have \<open>pval p x > 0\<close>
    by (simp add: \<open>pnorm p x < 1\<close> \<open>prime p\<close> \<open>x \<noteq> 0\<close> pnorm_pval_g_zero_D)
  hence \<open>multiplicity p (fst (quotient_of x)) > 0\<close>
    unfolding pval_def
    by linarith
  hence \<open>p dvd (fst (quotient_of x))\<close>
    using gr_implies_not0 not_dvd_imp_multiplicity_0 
    by blast
  moreover have \<open>\<not> (p dvd (snd (quotient_of x)))\<close>
    using \<open>p dvd (fst (quotient_of x))\<close> \<open>prime p\<close> prime_nat_int_transfer quotient_of_dvd_or 
      not_prime_unit 
    by blast    
  ultimately show ?thesis 
    by blast
qed

subsection \<open>Inverse\<close>

lemma multiplicity_quotient_fst: 
  \<open>(multiplicity p (fst (quotient_of (1 / x)))) = (multiplicity p (snd (quotient_of x)))\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis
    by (simp add: True) 
next
  case False
  hence \<open>x \<noteq> 0\<close>
    by blast
  show ?thesis 
  proof(cases \<open>x > 0\<close>)
    case True
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u > 0 \<and> v > 0\<close>
      by (metis \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff)
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u > 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (v, u)\<close>
    proof-
      have \<open>1/x = Fract v u\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd v u = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      ultimately show ?thesis
        unfolding quotient_of_def
        using \<open>u > 0\<close> quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  next
    case False
    hence \<open>x < 0\<close>
      using \<open>x \<noteq> 0\<close> 
      by simp
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u < 0 \<and> v > 0\<close>
      using \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff
    proof -
      have "\<forall>r. \<exists>i ia. x \<noteq> 0 \<and> 0 < i \<and> (r = 0 \<or> coprime ia i) \<and> (r = 0 \<or> Fract ia i = r)"
        by (metis (full_types) Rat_cases_nonzero \<open>x \<noteq> 0\<close>)
      thus ?thesis
        by (metis (no_types) Fract_less_zero_iff \<open>x < 0\<close> coprime_imp_gcd_eq_1)
    qed
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u < 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (-v, -u)\<close>
    proof-
      have \<open>1/x = Fract (-v) (-u)\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd (-v) (-u) = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      moreover have \<open>-u > 0\<close>
        using \<open>u < 0\<close>
        by simp
      ultimately show ?thesis
        unfolding quotient_of_def
        using quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
qed

lemma multiplicity_quotient_snd: 
  \<open>multiplicity p (snd (quotient_of (1 / x))) = multiplicity p (fst (quotient_of x))\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis
    by (simp add: True) 
next
  case False
  hence \<open>x \<noteq> 0\<close>
    by blast
  show ?thesis 
  proof(cases \<open>x > 0\<close>)
    case True
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u > 0 \<and> v > 0\<close>
      by (metis \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff)
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u > 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (v, u)\<close>
    proof-
      have \<open>1/x = Fract v u\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd v u = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      ultimately show ?thesis
        unfolding quotient_of_def
        using \<open>u > 0\<close> quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  next
    case False
    hence \<open>x < 0\<close>
      using \<open>x \<noteq> 0\<close> 
      by simp
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u < 0 \<and> v > 0\<close>
      using \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff
    proof -
      have "\<forall>r. \<exists>i ia. x \<noteq> 0 \<and> 0 < i \<and> (r = 0 \<or> coprime ia i) \<and> (r = 0 \<or> Fract ia i = r)"
        by (metis (full_types) Rat_cases_nonzero \<open>x \<noteq> 0\<close>)
      thus ?thesis
        by (metis (no_types) Fract_less_zero_iff \<open>x < 0\<close> coprime_imp_gcd_eq_1)
    qed
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u < 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (-v, -u)\<close>
    proof-
      have \<open>1/x = Fract (-v) (-u)\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd (-v) (-u) = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      moreover have \<open>-u > 0\<close>
        using \<open>u < 0\<close>
        by simp
      ultimately show ?thesis
        unfolding quotient_of_def
        using quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
qed

lemma pval_inverse:
  \<open>prime p \<Longrightarrow> pval p (1/x) = - pval p x\<close>
proof-
  assume \<open>prime p\<close>
  have \<open>pval p (1/x) = int (multiplicity p (fst (quotient_of (1 / x)))) -
    int (multiplicity p (snd (quotient_of (1 / x))))\<close>
    unfolding pval_def
    by blast
  also have \<open>\<dots> = int (multiplicity p (snd (quotient_of x))) -
    int (multiplicity p (fst (quotient_of x)))\<close>
  proof-
    have \<open>(multiplicity p (fst (quotient_of (1 / x))))  = (multiplicity p (snd (quotient_of x)))\<close>
      by (simp add: multiplicity_quotient_fst)      
    moreover have \<open>multiplicity p (snd (quotient_of (1 / x))) = multiplicity p (fst (quotient_of x))\<close>
      by (simp add: multiplicity_quotient_snd)      
    ultimately show ?thesis 
      by simp
  qed
  also have \<open>\<dots> = - (pval p x)\<close>
    unfolding pval_def 
    by simp
  finally show ?thesis
    by blast
qed

subsection \<open>Existence and uniqueness of decomposition\<close>

lemma pval_uniq:
  \<open>prime p \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x = (p powr (of_int l)) * y \<Longrightarrow> pval p y = 0 \<Longrightarrow> pval p x = l\<close>
proof-
  {
    have \<open>prime p \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x = (p powr (of_int l)) * y \<Longrightarrow> pval p y = 0 \<Longrightarrow> l \<ge> 0 
          \<Longrightarrow> pval p x = l\<close>
      for p y x l
    proof-
      assume \<open>prime p\<close> and \<open>y \<noteq> 0\<close> and \<open>x = (p powr (of_int l)) * y\<close> and \<open>pval p y = 0\<close> and \<open>l \<ge> 0\<close>
      have \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
        by (simp add: Fract_of_int_quotient quotient_of_div)
      have \<open>p > 0\<close>
        using \<open>prime p\<close>
        by (simp add: prime_gt_0_nat)
      have \<open>x = p^(nat l) * y\<close>
      proof-
        have \<open>p powr (of_int l) =  p^(nat l)\<close>
          using \<open>l \<ge> 0\<close> Transcendental.powr_realpow[where x = p and n = "nat l"]  \<open>p > 0\<close>
          by simp
        thus ?thesis
          by (simp add: \<open>of_rat x = complex_of_real (real p powr real_of_int l) * of_rat y\<close>)
      qed
      also have \<open>\<dots> = p^(nat l) * Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
        using \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
        by simp      
      also have \<open>\<dots> = (Fract (p^(nat l)) 1) * (Fract ((fst (quotient_of y))) (snd (quotient_of y)))\<close>
      proof-
        have \<open>p^(nat l) = Fract (p^(nat l)) 1\<close>
          by (metis Fract_of_nat_eq of_rat_of_nat_eq)        
        thus ?thesis
          by (metis of_rat_mult)        
      qed
      also have \<open>\<dots> = Fract (p^(nat l) * (fst (quotient_of y))) (snd (quotient_of y))\<close>
        by simp
      finally have \<open>x = (Fract ((p ^ nat l) * fst (quotient_of y)) (snd (quotient_of y)))\<close>
        by simp
      moreover have \<open>coprime ((p ^ nat l) * fst (quotient_of y)) (snd (quotient_of y))\<close>
      proof-
        have \<open>coprime (fst (quotient_of y)) (snd (quotient_of y))\<close>
          by (simp add: quotient_of_coprime)
        moreover have \<open>coprime (p ^ nat l) (snd (quotient_of y))\<close>
          by (metis Fract_less_zero_iff \<open>prime p\<close> \<open>pval p y = 0\<close> \<open>y = Fract (fst (quotient_of y)) 
          (snd (quotient_of y))\<close> calculation coprime_absorb_left coprime_commute
              coprime_power_left_iff dvd_0_right int.lless_eq is_unit_right_imp_coprime nat_0_iff 
              neq0_conv of_nat_power prime_imp_coprime_int prime_nat_int_transfer pval_unit_dvd 
              quotient_of_denom_pos' zero_less_Fract_iff zero_less_nat_eq)
        ultimately show ?thesis
          using coprime_mult_left_iff 
          by blast 
      qed
      moreover have \<open>snd (quotient_of y) > 0\<close>
        by (simp add: quotient_of_denom_pos')
      ultimately have \<open>quotient_of x = ((p^(nat l)) * fst (quotient_of y), snd (quotient_of y))\<close>
        by (simp add: quotient_of_Fract)
      have \<open>pval p x = int (multiplicity p (fst (quotient_of x)) )
                   - int (multiplicity p (snd (quotient_of x)) )\<close>
        unfolding pval_def 
        by blast
      also have \<open>\<dots> = int (multiplicity p ((p^(nat l)) * fst (quotient_of y)) )
                  - int (multiplicity p (snd (quotient_of y)) )\<close>
        using \<open>quotient_of x = ((p^(nat l)) * fst (quotient_of y), snd (quotient_of y))\<close>
        by simp
      also have \<open>\<dots> = int (multiplicity p ((p^(nat l)) * fst (quotient_of y)) )\<close>
      proof-
        have \<open>multiplicity p (snd (quotient_of y)) = 0\<close>
          by (metis \<open>prime p\<close> \<open>pval p y = 0\<close> dvd_refl multiplicity_unit_right 
              not_dvd_imp_multiplicity_0 pval_unit_dvd rat_zero_code snd_conv)        
        thus ?thesis 
          by simp
      qed
      also have \<open>\<dots> = l\<close>
      proof-
        have \<open>l \<le> multiplicity  p ((p ^ nat l) * fst (quotient_of y))\<close>
        proof-
          have \<open>(p ^ nat l) * fst (quotient_of y) \<noteq> 0\<close>
          proof-
            have \<open>p ^ nat l \<noteq> 0\<close>
              using \<open>prime p\<close>
              by auto
            moreover have \<open>fst (quotient_of y) \<noteq> 0\<close>
              using \<open>y \<noteq> 0\<close>
              by (metis Zero_rat_def \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close> 
                  eq_rat(3))
            ultimately show ?thesis 
              by simp
          qed
          moreover have \<open>(p ^ nat l) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
            by simp          
          moreover have \<open>\<not> is_unit (int p)\<close>
            using \<open>prime p\<close>
            by auto
          ultimately show ?thesis 
            using multiplicity_geI[where x = "(p ^ nat l) * fst (quotient_of y)" 
                and p = p and n = "nat l"]
            by simp
        qed
        moreover have \<open>multiplicity p ((p ^ nat l) * fst (quotient_of y)) < l + 1\<close>
        proof(rule classical)
          assume \<open>\<not> (multiplicity p ((p ^ nat l) * fst (quotient_of y)) < l + 1)\<close>
          hence \<open>multiplicity p ((p ^ nat l) * fst (quotient_of y)) \<ge> l + 1\<close>
            by simp
          hence \<open>(p ^ (nat l+1)) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
            using multiplicity_dvd'[where n = "nat l + 1" and p = p 
                and x = "(p ^ nat l) * fst (quotient_of y)"] \<open>l \<ge> 0\<close> 
            by auto
          hence \<open>((p ^ nat l)*p) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
            by simp
          hence \<open>p dvd (fst (quotient_of y))\<close>
            using \<open>prime p\<close> 
            by auto
          thus ?thesis
            using \<open>prime p\<close> \<open>pval p y = 0\<close> \<open>y \<noteq> 0\<close> pval_unit_dvd 
            by blast 
        qed
        ultimately show ?thesis 
          by simp
      qed
      finally show ?thesis
        by simp 
    qed  } note pval_uniq' = this

  assume \<open>prime p\<close> and \<open>y \<noteq> 0\<close> and \<open>x = (p powr (of_int l)) * y\<close> and \<open>pval p y = 0\<close>
  show ?thesis
  proof(cases \<open>l \<ge> 0\<close>)
    case True
    thus ?thesis
      using \<open>of_rat x = complex_of_real (real p powr real_of_int l) * of_rat y\<close> \<open>prime p\<close> 
        \<open>pval p y = 0\<close> \<open>y \<noteq> 0\<close> pval_uniq' 
      by blast 
  next
    case False
    define l' where \<open>l' = -l\<close>
    have \<open>l' \<ge> 0\<close>
      using False l'_def 
      by linarith
    define x' where \<open>x' = 1/x\<close>
    define y' where \<open>y' = 1/y\<close>
    have \<open>y' \<noteq> 0\<close>
      unfolding y'_def
      by (simp add: \<open>y \<noteq> 0\<close>)
    moreover have \<open>x' = (p powr (of_int l')) * y'\<close>
    proof-
      have \<open>x' = 1/((p powr (of_int l)) * y)\<close>
        unfolding  x'_def
        using \<open>x = (p powr (of_int l)) * y\<close>
        by (simp add: of_rat_divide)
      also have \<open>\<dots> = (1/(p powr (of_int l)))*(1/y)\<close>
        by (simp add: \<open>y \<noteq> 0\<close> nonzero_of_rat_divide)
      also have \<open>\<dots> = (1/(p powr (of_int l)))*y'\<close>
        unfolding y'_def
        by simp
      also have \<open>\<dots> = (p powr (- of_int l))*y'\<close>
        by (simp add: divide_powr_uminus)
      also have \<open>\<dots> = (p powr (of_int l'))*y'\<close>
        unfolding l'_def
        by simp
      finally show ?thesis
        by blast
    qed
    moreover have  \<open>pval p y' = 0\<close>
      unfolding y'_def
      by (simp add: \<open>prime p\<close> \<open>pval p y = 0\<close> pval_inverse)
    ultimately have \<open>pval p x' = l'\<close>
      using \<open>0 \<le> l'\<close> \<open>prime p\<close> pval_uniq'
      by auto
    thus \<open>pval p x = l\<close>
      unfolding x'_def l'_def
      using \<open>prime p\<close> pval_inverse 
      by simp
  qed
qed

lemma pval_decomposition:
  \<open>prime p \<Longrightarrow> \<exists> y. (x::rat) = (p powr (of_int (pval p x))) * y \<and> pval p y = 0\<close>
proof(cases \<open>x = 0\<close>)
  case True
  assume \<open>prime p\<close>
  define y::rat where \<open>y = 0\<close>
  have \<open>x = (p powr (of_int (pval p x))) * y\<close> 
    unfolding y_def
    by (simp add: True)    
  moreover  have \<open>pval p y = 0\<close>
    unfolding y_def
    using pval_zero \<open>prime p\<close>
    by simp
  ultimately show ?thesis 
    by blast
next
  case False
  assume \<open>prime p\<close>
  hence \<open>\<not> ( p dvd (fst (quotient_of x)) ) \<or>  \<not> ( p dvd (snd (quotient_of x)) )\<close>
    using prime_nat_int_transfer quotient_of_dvd_or not_prime_unit 
    by blast         
  show ?thesis
  proof(cases \<open>\<not> ( p dvd (snd (quotient_of x)) )\<close>)
    case True
    hence \<open>multiplicity p (snd (quotient_of x)) = 0\<close>
      using not_dvd_imp_multiplicity_0 
      by auto
    hence \<open>pval p x = int (multiplicity p (fst (quotient_of x))) -
    int (multiplicity p (snd (quotient_of x)))\<close>
      unfolding pval_def
      by blast
    also have \<open>\<dots> = (multiplicity p (fst (quotient_of x)))\<close>
      by (simp add: \<open>multiplicity p (snd (quotient_of x)) = 0\<close>)
    finally have \<open>pval p x = multiplicity p (fst (quotient_of x))\<close>
      by blast
    hence \<open>pval p x \<ge> 0\<close>
      by simp      
    have \<open>(p ^ (nat (pval p x))) dvd fst (quotient_of x)\<close>
      using multiplicity_dvd \<open>pval p x = multiplicity p (fst (quotient_of x))\<close>
      by simp
    hence \<open>\<exists> k::int. fst (quotient_of x) = p ^ (nat (pval p x)) * k\<close>
      by auto
    then obtain k::int where \<open>fst (quotient_of x) = p ^ (nat (pval p x)) * k\<close>
      by blast
    have \<open>multiplicity p k = 0\<close>
    proof(rule classical)
      assume \<open>\<not> (multiplicity p k = 0)\<close>
      hence \<open>multiplicity p k \<ge> 1\<close>
        by auto
      hence \<open>p dvd k\<close>
        by (meson \<open>multiplicity p k \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      hence \<open>(p ^ (nat (pval p x)+1)) dvd (p ^ (nat (pval p x))*k)\<close>
        by simp
      hence \<open>(p ^ (nat (pval p x)+1)) dvd (fst (quotient_of x))\<close>
        by (simp add: \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close>)
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> nat (pval p x)+1\<close>
        using multiplicity_geI
        by (metis \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close> \<open>multiplicity p k \<noteq> 0\<close> 
            \<open>prime p\<close> multiplicity_unit_left multiplicity_zero no_zero_divisors not_prime_0 
            of_nat_eq_0_iff of_nat_power power_not_zero)
      thus ?thesis
        by (simp add: \<open>pval p x = int (multiplicity p (fst (quotient_of x)))\<close>)
    qed
    define y where \<open>y = Fract k (snd (quotient_of x))\<close>
    have \<open>pval p y = 0\<close>
    proof-
      have \<open>coprime k (snd (quotient_of x))\<close>
        by (metis \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close> coprime_mult_left_iff 
            prod.exhaust_sel quotient_of_coprime)        
      hence \<open>quotient_of y = (k, snd (quotient_of x))\<close>
        by (simp add: quotient_of_Fract quotient_of_denom_pos' y_def)
      have \<open>pval p y =  int (multiplicity p (fst (quotient_of y))) -
                        int (multiplicity p (snd (quotient_of y)))\<close>
        unfolding pval_def
        by blast
      moreover have \<open>multiplicity p (fst (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity p k = 0\<close> \<open>quotient_of y = (k, snd (quotient_of x))\<close> y_def 
        by auto        
      moreover have \<open>multiplicity p (snd (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity p (snd (quotient_of x)) = 0\<close>
          \<open>quotient_of y = (k, snd (quotient_of x))\<close> y_def 
        by auto
      ultimately show ?thesis
        by simp
    qed
    have \<open>x = (fst (quotient_of x))/ (snd (quotient_of x))\<close>
      by (metis (mono_tags, lifting) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
          quotient_of_div surjective_pairing)
    also have \<open>\<dots> = (p ^ (nat (pval p x)) * k)/ (snd (quotient_of x))\<close>
      by (simp add: \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close>)
    also have \<open>\<dots> = p ^ (nat (pval p x)) * (k/ (snd (quotient_of x)))\<close>
      by simp
    also have \<open>\<dots> = p ^ (nat (pval p x)) * y\<close>
      unfolding y_def
      by (metis True dvd_0_right of_rat_rat of_real_divide of_real_mult of_real_of_int_eq 
          of_real_of_nat_eq)      
    finally have \<open>x = p ^ (nat (pval p x)) * y\<close>
      by blast
    moreover have \<open>p powr (of_int (pval p x)) = p ^ (nat (pval p x))\<close>
      using \<open>pval p x \<ge> 0\<close>
      by (metis \<open>prime p\<close> of_nat_0_less_iff of_nat_nat of_nat_power powr_realpow prime_gt_0_nat) 
    ultimately have \<open>x = (p powr (of_int (pval p x))) * y\<close>
      by simp
    thus ?thesis
      using \<open>pval p y = 0\<close>
      by blast
  next
    case False
    hence \<open>\<not> ( p dvd (fst (quotient_of x)) )\<close>
      using \<open>\<not> int p dvd fst (quotient_of x) \<or> \<not> int p dvd snd (quotient_of x)\<close>
      by auto      
    hence \<open>multiplicity p (fst (quotient_of x)) = 0\<close>
      using not_dvd_imp_multiplicity_0 
      by auto
    hence \<open>pval p x = int (multiplicity p (fst (quotient_of x))) -
    int (multiplicity p (snd (quotient_of x)))\<close>
      unfolding pval_def
      by blast
    also have \<open>\<dots> = -(multiplicity p (snd (quotient_of x)))\<close>
      by (simp add: \<open>multiplicity p (fst (quotient_of x)) = 0\<close>)
    finally have \<open>pval p x = -multiplicity p (snd (quotient_of x))\<close>
      by blast
    hence \<open>pval p x \<le> 0\<close>
      by simp      
    have \<open>(p ^ (nat (-pval p x))) dvd snd (quotient_of x)\<close>
      using multiplicity_dvd
      by (simp add: multiplicity_dvd \<open>pval p x = - int (multiplicity p (snd (quotient_of x)))\<close>) 
    hence \<open>\<exists> k::int. snd (quotient_of x) = p ^ (nat (-pval p x)) * k\<close>
      by auto
    then obtain k::int where \<open>snd (quotient_of x) = p ^ (nat (-pval p x)) * k\<close>
      by blast
    have \<open>multiplicity p k = 0\<close>
    proof(rule classical)
      assume \<open>\<not> (multiplicity p k = 0)\<close>
      hence \<open>multiplicity p k \<ge> 1\<close>
        by auto
      hence \<open>p dvd k\<close>
        by (meson \<open>multiplicity p k \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      hence \<open>(p ^ (nat (-pval p x)+1)) dvd (p ^ (nat (-pval p x))*k)\<close>
        by simp
      hence \<open>(p ^ (nat (-pval p x)+1)) dvd (snd (quotient_of x))\<close>
        by (simp add: \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>)
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> nat (-pval p x)+1\<close>
        using multiplicity_geI \<open>1 \<le> multiplicity p k\<close> \<open>pval p x \<le> 0\<close>
        by (metis \<open>multiplicity p k \<noteq> 0\<close> \<open>prime p\<close>
            \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close> divisors_zero 
            multiplicity_unit_left multiplicity_zero not_prime_0 of_nat_eq_0_iff of_nat_power 
            power_not_zero) 
      thus ?thesis
        by (simp add: \<open>pval p x = - int (multiplicity p (snd (quotient_of x)))\<close>)        
    qed
    define y where \<open>y = Fract (fst (quotient_of x)) k\<close>
    have \<open>pval p y = 0\<close>
    proof-
      have \<open>coprime (fst (quotient_of x)) k\<close>
        by (metis \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close> coprime_mult_right_iff 
            prod.collapse quotient_of_coprime)
      moreover have \<open>k > 0\<close>
      proof-
        have \<open>snd (quotient_of x) > 0\<close>
          by (simp add: quotient_of_denom_pos')
        thus ?thesis
          using  \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>
          by (simp add: zero_less_mult_iff)
      qed
      ultimately have \<open>quotient_of y = (fst (quotient_of x), k)\<close>
        unfolding y_def
        by (simp add: quotient_of_Fract)          
      have \<open>pval p y =  int (multiplicity p (fst (quotient_of y))) -
                        int (multiplicity p (snd (quotient_of y)))\<close>
        unfolding pval_def
        by blast
      moreover have \<open>multiplicity p (fst (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity p (fst (quotient_of x)) = 0\<close> 
          \<open>quotient_of y = (fst (quotient_of x), k)\<close> y_def 
        by auto
      moreover have \<open>multiplicity p (snd (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity p k = 0\<close> \<open>quotient_of y = (fst (quotient_of x), k)\<close> y_def 
        by auto
      ultimately show ?thesis
        by simp
    qed
    have \<open>x = (fst (quotient_of x))/ (snd (quotient_of x))\<close>
      by (metis (mono_tags, lifting) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
          quotient_of_div surjective_pairing)
    also have \<open>\<dots> = (fst (quotient_of x))/(p ^ (nat (-pval p x)) * k)\<close>
      by (simp add: \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>)      
    also have \<open>\<dots> = (1/(p ^ (nat (-pval p x)))) * ((fst (quotient_of x))/k)\<close>
      by simp
    also have \<open>\<dots> = (1/(p ^ (nat (-pval p x)))) * y\<close>
    proof-
      have \<open>Fract (fst (quotient_of x)) k = (fst (quotient_of x))/k\<close>
        by (metis (no_types, hide_lams) division_ring_divide_zero of_int_0_eq_iff of_rat_0 
            of_rat_rat of_real_divide of_real_of_int_eq rat_number_collapse(6))
      thus ?thesis
        unfolding y_def
        by simp
    qed
    finally have \<open>x = (1/(p ^ (nat (-pval p x)))) * y\<close>
      by blast
    moreover have \<open>p powr (of_int (pval p x)) = 1/(p ^ (nat (-pval p x)))\<close>
      using \<open>pval p x \<le> 0\<close>
        \<open>prime p\<close> div_by_1 nat_0_iff not_prime_0 of_nat_le_0_iff of_nat_power power_0 powr_int
    proof -
      have "p \<noteq> 0"
        by (metis \<open>prime p\<close> not_prime_0)
      hence "\<not> int p \<le> 0"
        by auto
      hence "\<not> real p \<le> 0"
        by auto
      thus ?thesis
        by (simp add: \<open>pval p x \<le> 0\<close> powr_int)
    qed   
    ultimately have \<open>x = (p powr (of_int (pval p x))) * y\<close>
      by simp
    thus ?thesis
      using \<open>pval p y = 0\<close>
      by blast
  qed
qed

lemma pnorm_decomposition:
  \<open>prime p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> \<exists> y::rat. (x::rat) = (p powr (pval p x)) * y \<and> pnorm p y = 1\<close>
proof-
  assume \<open>prime p\<close> and \<open>x \<noteq> 0\<close>
  hence \<open>\<exists>y::rat. x = (p powr (pval p x)) * y \<and> pval p y = 0\<close>
    using pval_decomposition 
    by auto
  then obtain y::rat where \<open>x = (p powr (pval p x)) * y\<close> and \<open>pval p y = 0\<close>
    by blast
  have \<open>pnorm p y = 1\<close>
  proof-
    have \<open>y \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> \<open>x = (p powr (pval p x)) * y\<close>
      by auto
    hence \<open>pnorm p y = p powr (- (pval p y))\<close>
      using pnorm_simplified 
      by auto
    thus ?thesis
      using \<open>prime p\<close> \<open>pval p y = 0\<close> of_nat_0_eq_iff 
      by auto      
  qed
  thus ?thesis 
    using \<open>x = (p powr (pval p x)) * y\<close>
    by blast
qed

subsection \<open>Addition and multiplication\<close>

lemma pval_additivity:
  \<open>prime p \<Longrightarrow> u \<noteq> 0 \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> pval p (u * v) = (pval p u) + (pval p v)\<close>
proof-
  {
    have \<open>prime p \<Longrightarrow> u \<noteq> 0 \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> pval p u = 0 \<Longrightarrow> pval p v = 0 \<Longrightarrow> pval p (u * v) = 0\<close>
      for p u v
    proof-
      assume \<open>prime p\<close> and \<open>u \<noteq> 0\<close> and \<open>v \<noteq> 0\<close> and \<open>pval p u = 0\<close> and \<open>pval p v = 0\<close>
      have \<open>\<not>(p dvd (fst (quotient_of u)))\<close>
        using \<open>pval p u = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>u \<noteq> 0\<close> 
        by blast
      moreover have \<open>\<not>(p dvd (fst (quotient_of v)))\<close>
        using \<open>pval p v = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>v \<noteq> 0\<close> 
        by blast
      ultimately have \<open>\<not>(p dvd ((fst (quotient_of u))*(fst (quotient_of v))))\<close>
        by (meson \<open>prime p\<close> prime_dvd_multD prime_nat_int_transfer)
      have \<open>\<not>(p dvd (snd (quotient_of u)))\<close>
        using \<open>pval p u = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>u \<noteq> 0\<close> 
        by blast
      moreover have \<open>\<not>(p dvd (snd (quotient_of v)))\<close>
        using \<open>pval p v = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>v \<noteq> 0\<close> 
        by blast
      ultimately have \<open>\<not>(p dvd ((snd (quotient_of u))*(snd (quotient_of v))))\<close>
        by (meson \<open>prime p\<close> prime_dvd_multD prime_nat_int_transfer)
      have \<open>u * v =  ((fst (quotient_of u))*(fst (quotient_of v))) /
                 ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
      proof-
        have \<open>u = (fst (quotient_of u)) / (snd (quotient_of u))\<close>
        proof -
          have f1: "u = rat_of_int (fst (quotient_of u)) / rat_of_int (snd (quotient_of u))"
            by (meson prod.exhaust_sel quotient_of_div)
          have "rat_of_int (snd (quotient_of u)) \<noteq> 0"
            by (metis (no_types) \<open>\<not> int p dvd snd (quotient_of u)\<close> dvd_0_right of_int_eq_0_iff)
          thus ?thesis
            using f1 by (metis (full_types) nonzero_of_rat_divide of_rat_of_int_eq of_real_divide 
                of_real_of_int_eq)
        qed
        moreover have \<open>v = (fst (quotient_of v)) / (snd (quotient_of v))\<close>
        proof -
          have f1: "v = rat_of_int (fst (quotient_of v)) / rat_of_int (snd (quotient_of v))"
            by (meson prod.exhaust_sel quotient_of_div)
          have "rat_of_int (snd (quotient_of v)) \<noteq> 0"
            by (metis \<open>\<not> int p dvd snd (quotient_of v)\<close> dvd_0_right of_int_eq_0_iff)
          thus ?thesis
            using f1 by (metis (full_types) nonzero_of_rat_divide of_rat_of_int_eq 
                of_real_divide of_real_of_int_eq)
        qed      
        ultimately show ?thesis
          by (simp add: of_rat_mult) 
      qed
      hence \<open>u * v =  Fract ((fst (quotient_of u))*(fst (quotient_of v))) 
                 ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
        by (metis (no_types, lifting) \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> divide_eq_0_iff divisors_zero of_int_0_eq_iff
            of_rat_0 of_rat_eq_iff of_rat_rat of_real_divide of_real_of_int_eq)
      define d where \<open>d = gcd ((fst (quotient_of u))*(fst (quotient_of v))) 
                              ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
      define z::\<open>int*int\<close> where \<open>z = ( ((fst (quotient_of u))*(fst (quotient_of v))) div d, 
                                  ((snd (quotient_of u))*(snd (quotient_of v))) div d )\<close>

      have \<open>u * v =  Fract (fst z) (snd z)\<close>
        unfolding z_def
        by (simp add: Fract_coprime \<open>u * v = Fract (fst (quotient_of u)
             * fst (quotient_of v)) (snd (quotient_of u) * snd (quotient_of v))\<close> d_def)
      moreover have \<open>snd z > 0\<close>
      proof-
        have \<open>snd (quotient_of u) > 0\<close>
          by (simp add: quotient_of_denom_pos')
        moreover have \<open>snd (quotient_of v) > 0\<close>
          by (simp add: quotient_of_denom_pos')      
        moreover have \<open>d \<noteq> 0\<close>
          unfolding d_def
          using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> by auto
        ultimately show ?thesis 
          unfolding z_def
          by (smt \<open>u * v = Fract (fst z) (snd z)\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> d_def gcd_pos_int mult_pos_pos 
              no_zero_divisors pos_imp_zdiv_neg_iff rat_number_collapse(6) snd_conv z_def)
      qed
      moreover have \<open>coprime (fst z) (snd z)\<close>
        unfolding z_def
        using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> d_def div_gcd_coprime 
          dvd_0_right
        by (metis fst_conv snd_conv)
      ultimately have \<open>u * v = Fract (fst z) (snd z) \<and>
        (0::int) < snd z \<and> coprime (fst z) (snd z)\<close>
        by auto
      hence \<open>quotient_of (u * v) = z\<close>
        unfolding quotient_of_def
        using quotient_of_unique 
        by blast
      hence \<open>fst (quotient_of (u * v)) dvd ((fst (quotient_of u))*(fst (quotient_of v)))\<close>
        unfolding z_def
        by (metis d_def dvd_mult_div_cancel dvd_triv_right fst_conv gcd_dvd1)
      hence \<open>\<not>(p dvd fst (quotient_of (u * v)))\<close>
        using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> dvd_trans 
        by blast
      from \<open>quotient_of (u * v) = z\<close>
      have \<open>snd (quotient_of (u * v)) dvd ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
        unfolding z_def
        by (metis d_def dvd_def dvd_div_mult_self gcd_dvd2 snd_conv)    
      hence \<open>\<not>(p dvd snd (quotient_of (u * v)))\<close>
        using \<open>\<not> int p dvd snd (quotient_of u) * snd (quotient_of v)\<close> dvd_trans 
        by blast    
      thus ?thesis 
        using \<open>\<not>(p dvd fst (quotient_of (u * v)))\<close>
        by (simp add: \<open>prime p\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> pval_unit_dvd_D)
    qed  
  } note pval_composition_of_units = this

  assume \<open>prime p\<close> and \<open>u \<noteq> 0\<close> and \<open>v \<noteq> 0\<close>
  hence \<open>\<exists> y. u = ((of_int p) powr (of_int (pval p u))) * y \<and> pval p y = 0\<close>
    using pval_decomposition[where p = "p" and x = "u"]
    by simp
  then obtain yu where \<open>u = ((of_int p) powr (of_int (pval p u))) * yu\<close> and \<open>pval p yu = 0\<close>
    by blast
  have \<open>\<exists> y. v = ((of_int p) powr (of_int (pval p v))) * y \<and> pval p y = 0\<close>
    using pval_decomposition[where p = "p" and x = "v"] \<open>prime p\<close>
    by simp
  then obtain yv where \<open>v = ((of_int p) powr (of_int (pval p v))) * yv\<close> and \<open>pval p yv = 0\<close>
    by blast
  have \<open>u * v = ( ((of_int p) powr (of_int (pval p u))) * ((of_int p) powr (of_int (pval p v))) ) 
                 * (yu * yv)\<close> 
    using \<open>u = ((of_int p) powr (of_int (pval p u))) * yu\<close>
      \<open>v = ((of_int p) powr (of_int (pval p v))) * yv\<close>
    by (simp add: of_rat_mult)
  also have  \<open>\<dots> = ((of_int p) powr (of_int (pval p u + pval p v)) )  * (yu * yv)\<close> 
  proof-
    have \<open>p powr (pval p u) * p powr (pval p v) = p powr (pval p u + pval p v)\<close>
      using Transcendental.powr_add[where x = "((of_int p)::real)" 
          and a = "(of_int (pval p u))::real" 
          and b = "(of_int (pval p v))::real"]
      by auto
    moreover have \<open>pval p u + pval p v = pval p u + pval p v\<close>
      by auto
    ultimately have \<open>((of_int p) powr (of_int (pval p u))) * ((of_int p) powr (of_int (pval p v)))
                   = (of_int p) powr (real_of_int (pval p u + pval p v)) \<close>
      by auto
    thus ?thesis
      by (metis (no_types) \<open>of_int (int p) powr of_int (pval p u) * of_int (int p) powr 
        of_int (pval p v) = of_int (int p) powr of_int (pval p u + pval p v)\<close> of_real_mult)
  qed
  finally have \<open>u * v = complex_of_real ((int p) powr (pval p u + pval p v)) * (yu * yv)\<close>
    by blast
  moreover have \<open>pval p (yu * yv) = 0\<close>
    using pval_composition_of_units \<open>prime p\<close> \<open>pval p yu = 0\<close> \<open>pval p yv = 0\<close>
    by (metis mult_eq_0_iff)        
  ultimately show ?thesis
    using pval_uniq[where p = "p" and x = "u * v" and l = "pval p u + pval p v" and y = "yu * yv"]
      \<open>prime p\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> 
    by force 
qed

lemma pnorm_multiplicativity:
  \<open>prime p \<Longrightarrow> pnorm p (u * v) = (pnorm p u) * (pnorm p v)\<close>
proof(cases \<open>u * v = 0\<close>)
  case True
  hence \<open>u = 0 \<or> v = 0\<close>
    by (simp add: True divisors_zero)
  have \<open>pnorm p (u * v) = 0\<close>
    unfolding pnorm_def
    by (simp add: True)
  show ?thesis
  proof(cases \<open>u = 0\<close>)
    case True
    hence \<open>pnorm p u = 0\<close>
      unfolding pnorm_def
      by auto
    thus ?thesis
      by (simp add: \<open>pnorm p (u * v) = 0\<close>)
  next
    case False
    hence \<open>v = 0\<close>
      using \<open>u = 0 \<or> v = 0\<close> 
      by blast
    hence \<open>pnorm p v = 0\<close>
      unfolding pnorm_def
      by auto
    thus ?thesis
      by (simp add: \<open>pnorm p (u * v) = 0\<close>)
  qed
next
  case False
  hence \<open>u \<noteq> 0\<close>
    by simp
  hence \<open>v \<noteq> 0\<close>
    using False
    by simp
  assume \<open>prime p\<close>
  have \<open>pnorm p (u * v) = p powr (-(pval p (u * v)))\<close>
    using pnorm_simplified[where p = "p" and x = "u * v"]
      False by blast    
  also have \<open>\<dots> = p powr (-(pval p u) - (pval p v))\<close>
  proof-
    have \<open>pval p (u * v) = (pval p u) + (pval p v)\<close>
      using \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close>  \<open>prime p\<close> pval_additivity[where p = "p" and u = "u" and v = "v"]
      by blast
    hence \<open>-(pval p (u * v)) = -(pval p u) - (pval p v)\<close>
      by simp
    thus ?thesis
      by simp 
  qed
  also have \<open>\<dots> = (p powr (-(pval p u)))*(p powr (- (pval p v)))\<close>
    by (metis linordered_field_class.sign_simps(2) of_int_add powr_add uminus_add_conv_diff)    
  also have \<open>\<dots> = (pnorm p u)*(pnorm p v)\<close>
    using \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> pnorm_simplified 
    by auto
  finally show ?thesis by blast
qed

subsection \<open>Unit ball\<close>

lemma pnorm_unit_ball:
  fixes n :: nat
  assumes \<open>prime p\<close> and \<open>pnorm p x = 1\<close> and \<open>pnorm p y < 1\<close>
  shows \<open>pnorm p (x + y) = 1\<close>
proof(cases \<open>y = 0\<close>)
  case True
  thus ?thesis
    by (simp add: assms(2))      
next
  case False
  obtain m n where \<open>quotient_of x = (m, n)\<close>
    using gcd.cases 
    by blast
  hence \<open>x = Fract m n\<close>
    using quotient_of_Fract quotient_of_coprime quotient_of_denom_pos quotient_of_inject 
    by auto
  have \<open>\<not> (p dvd m)\<close>
    using \<open>pnorm p x = 1\<close> \<open>prime p\<close> \<open>quotient_of x = (m, n)\<close> fst_conv pnorm_1_Fract
    by metis
  have \<open>\<not> (p dvd n)\<close>
    using \<open>pnorm p x = 1\<close> \<open>prime p\<close> \<open>quotient_of x = (m, n)\<close> snd_conv pnorm_1_Fract
    by metis
  obtain m' n' where \<open>quotient_of y = (m', n')\<close>
    using gcd.cases 
    by blast
  hence \<open>y = Fract m' n'\<close>
    using quotient_of_Fract quotient_of_coprime quotient_of_denom_pos quotient_of_inject 
    by auto
  from \<open>pnorm p y < 1\<close>
  have \<open>p dvd m'\<close>
    using \<open>y \<noteq> 0\<close> \<open>pnorm p y < 1\<close> \<open>prime p\<close> \<open>quotient_of y = (m', n')\<close> fst_conv pnorm_l_1_Fract
    by metis
  have \<open>\<not> (p dvd n')\<close>
    using \<open>y \<noteq> 0\<close> \<open>pnorm p y < 1\<close> \<open>prime p\<close> \<open>quotient_of y = (m', n')\<close> snd_conv pnorm_l_1_Fract
    by metis
  have \<open>x + y = Fract m n + Fract m' n'\<close>
    by (simp add: \<open>x = Fract m n\<close> \<open>y = Fract m' n'\<close>)
  also have \<open>\<dots> = Fract (m*n' + n*m') (n*n')\<close>
    by (metis False \<open>quotient_of x = (m, n)\<close> \<open>x = Fract m n\<close> \<open>y = Fract m' n'\<close> add_rat
        divides_aux_eq int.zero_not_one mult.commute rat_number_collapse(6) rat_zero_code)
  finally have \<open>x + y = Fract (m*n' + n*m') (n*n')\<close>
    by blast
  have \<open>\<not> (p dvd fst (quotient_of (x+y)))\<close>
  proof-
    have \<open>\<not> (p dvd m*n' + n*m')\<close>
    proof-
      have \<open>p dvd (n*m')\<close>
        by (simp add: \<open>p dvd m'\<close>)        
      moreover have \<open>\<not>(p dvd (m*n'))\<close>
      proof -
        have "prime (int p)"
          by (metis assms(1) prime_nat_int_transfer)
        thus ?thesis
          by (metis \<open>\<not> int p dvd m\<close> \<open>\<not> int p dvd n'\<close> prime_dvd_multD)
      qed        
      ultimately show ?thesis
      proof -
        have "n * m' + m * n' = m * n' + n * m'"
          by simp
        thus ?thesis
          by (metis \<open>\<not> int p dvd m * n'\<close> \<open>int p dvd n * m'\<close> dvd_add_right_iff)
      qed 
    qed
    moreover have \<open>fst (quotient_of (x+y)) dvd (m*n' + n*m')\<close>
      by (metis \<open>x + y = Fract (m*n' + n*m') (n*n')\<close> \<open>\<not> int p dvd n'\<close> \<open>\<not> int p dvd n\<close> dvd_0_right 
          fst_quotient_of_divide mult_eq_0_iff)     
    ultimately show ?thesis
      using dvd_trans 
      by blast 
  qed
  moreover have \<open>\<not> (p dvd snd (quotient_of (x+y)))\<close>
  proof-
    have \<open>\<not>(p dvd (n*n'))\<close>
      by (meson \<open>\<not> int p dvd n'\<close> \<open>\<not> int p dvd n\<close> assms(1) prime_dvd_multD prime_nat_int_transfer)
    moreover have \<open>snd (quotient_of (x+y)) dvd (n*n')\<close>
      using \<open>x + y = Fract (m*n' + n*m') (n*n')\<close>
      by (simp add: snd_quotient_of_divide)      
    ultimately show ?thesis
      by auto
  qed
  ultimately show \<open>pnorm p (x+y) = 1\<close>
    by (metis assms(1) dvd_0_right fst_conv pnorm_pval_zero_I pval_unit_dvd_D rat_zero_code)    
qed

subsection \<open>Ultrametric inequality\<close>

lemma pnorm_ultrametric:
  assumes \<open>prime p\<close>
  shows \<open>pnorm p (x + y) \<le> max (pnorm p x) (pnorm p y)\<close>
proof-
  {
    have \<open>pnorm p x = pnorm p y \<Longrightarrow> pnorm p (x + y) \<le> pnorm p y\<close>
      for x y
    proof(cases \<open>x = 0\<close>)
      case True
      thus ?thesis
        by simp 
    next
      assume \<open>pnorm p x = pnorm p y\<close>
      case False
      hence \<open>x \<noteq> 0\<close>
        by blast
      moreover have \<open>y \<noteq> 0\<close>
      proof(rule classical)
        assume \<open>\<not>(y \<noteq> 0)\<close>
        hence \<open>y = 0\<close>
          by blast
        hence \<open>pnorm p y = 0\<close>
          by (simp add: assms pnorm_eq_zero)
        hence \<open>pnorm p x = 0\<close>
          using \<open>pnorm p x = pnorm p y\<close>
          by simp
        moreover have \<open>pnorm p x \<noteq> 0\<close>
          using \<open>prime p\<close> \<open>x \<noteq> 0\<close> pnorm_eq_zero_I 
          by blast
        ultimately show ?thesis
          by blast
      qed
      ultimately have \<open>pval p x = pval p y\<close>
        using \<open>prime p\<close> \<open>pnorm p x = pnorm p y\<close> pnorm_pval 
        by blast

      show ?thesis
      proof(cases \<open>x + y = 0\<close>)
        case True
        thus ?thesis
          by (simp add: assms pnorm_eq_zero_D pnorm_geq_zero) 
      next
        case False
        hence \<open>x + y \<noteq> 0\<close>
          by blast

        have \<open>\<exists> u::rat. x = (p powr (pval p x)) * u \<and> pnorm p u = 1\<close>
          using pnorm_decomposition
          by (simp add: \<open>x \<noteq> 0\<close> assms)
        then obtain u::rat where \<open>x = (p powr (pval p x)) * u\<close> and \<open>pnorm p u = 1\<close>
          by blast
        have \<open>\<exists> v::rat. y = (p powr (pval p y)) * v \<and> pnorm p v = 1\<close>
          using pnorm_decomposition
          by (simp add: \<open>y \<noteq> 0\<close> assms)
        then obtain v::rat where \<open>y = (p powr (pval p y)) * v\<close> and \<open>pnorm p v = 1\<close>
          by blast
        have \<open>y = (p powr (pval p x)) * v\<close>
          using  \<open>y = (p powr (pval p y)) * v\<close> \<open>pval p x = pval p y\<close>
          by simp
        have \<open>x + y = (p powr (pval p x)) * u + (p powr (pval p x)) * v\<close>
          by (simp add: \<open>of_rat x = complex_of_real (real p powr real_of_int (pval p x)) * of_rat u\<close>
              \<open>of_rat y = complex_of_real (real p powr real_of_int (pval p y)) * of_rat v\<close> 
              \<open>pval p x = pval p y\<close> of_rat_add)
        also have \<open>\<dots> = (p powr (pval p x)) * (u + v)\<close>
          by (simp add: linordered_field_class.sign_simps(18) of_rat_add)
        finally have \<open>x + y = (p powr (pval p x)) * (u + v)\<close>
          by simp
        have \<open>\<exists> k::nat. \<exists> w::rat. u + v = (p ^ k) * w \<and> pnorm p w = 1\<close>
        proof-
          have \<open>u = Fract (fst (quotient_of u)) (snd (quotient_of u))\<close>
            by (metis normalize_stable prod.collapse quotient_of_Fract quotient_of_coprime 
                quotient_of_denom_pos' quotient_of_inject)
          moreover have \<open>v = Fract (fst (quotient_of v)) (snd (quotient_of v))\<close>
            by (metis normalize_stable prod.collapse quotient_of_Fract quotient_of_coprime 
                quotient_of_denom_pos' quotient_of_inject)
          ultimately have \<open>u + v = Fract ((fst (quotient_of u))*(snd (quotient_of v)) 
                           + (snd (quotient_of u))*(fst (quotient_of v)))  
                          ( (snd (quotient_of u))*(snd (quotient_of v)) )\<close>
            by (metis add_rat less_int_code(1) mult.commute quotient_of_denom_pos')
          have \<open>snd (quotient_of (u+v)) dvd ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
            by (simp add: \<open>u + v = Fract (fst (quotient_of u) * snd (quotient_of v) 
          + snd (quotient_of u) * fst (quotient_of v)) (snd (quotient_of u) * snd (quotient_of v))\<close>
                snd_quotient_of_divide)
          moreover have \<open>\<not>(p dvd ((snd (quotient_of u))*(snd (quotient_of v))))\<close>
          proof-
            have \<open>\<not>(p dvd ((snd (quotient_of u))))\<close>
              by (simp add: \<open>pnorm p u = 1\<close> assms pnorm_1_Fract)            
            moreover have \<open>\<not>(p dvd ((snd (quotient_of v))))\<close>
              by (simp add: \<open>pnorm p v = 1\<close> assms pnorm_1_Fract)            
            ultimately show ?thesis
              by (meson assms prime_dvd_multD prime_nat_int_transfer)            
          qed
          ultimately have \<open>\<not>(p dvd (snd (quotient_of (u + v))))\<close>
            using dvd_trans 
            by blast
          have \<open>u + v \<noteq> 0\<close>
          proof(rule classical)
            assume \<open>\<not> (u + v \<noteq> 0)\<close>
            hence \<open>u + v = 0\<close>
              by blast
            hence \<open>x + y = 0\<close>
              using \<open>x + y = (p powr (pval p x)) * (u + v)\<close>
              by simp
            thus ?thesis
              using False 
              by auto                
          qed
          define k where \<open>k = multiplicity p (fst (quotient_of (u + v)))\<close>
          have \<open>\<exists> m::int. fst (quotient_of (u + v)) = p ^ k * m\<close>
            unfolding k_def
            by (metis dvd_def multiplicity_dvd of_nat_power)
          then obtain m::int where \<open>fst (quotient_of (u + v)) = p ^ k * m\<close>
            by blast
          have \<open>\<not> (p dvd m)\<close>
          proof(rule classical)
            assume \<open>\<not> (\<not> (p dvd m))\<close>
            hence \<open>p dvd m\<close>
              by blast
            hence \<open>(p^k * p) dvd (p^k * m)\<close>
              by auto
            hence \<open>p^(Suc k) dvd (p^k * m)\<close>
              by simp
            hence \<open>p^(Suc k) dvd (fst (quotient_of (u + v)))\<close>
              by (simp add: \<open>fst (quotient_of (u + v)) = int (p ^ k) * m\<close>)
            moreover have \<open>\<not> is_unit (int p)\<close>
              using assms 
              by auto            
            moreover have \<open>fst (quotient_of (u + v)) \<noteq> 0\<close>
            proof(rule classical)
              assume \<open>\<not> (fst (quotient_of (u + v)) \<noteq> 0)\<close>
              hence \<open>fst (quotient_of (u + v)) = 0\<close>
                by auto
              moreover have \<open>u + v = Fract (fst (quotient_of (u + v))) (snd (quotient_of (u + v)))\<close>
                unfolding quotient_of_def
                by (smt quotient_of_unique theI')             
              ultimately have \<open>u + v = 0\<close>
                using rat_number_collapse(1) 
                by auto
              thus ?thesis 
                using \<open>u + v \<noteq> 0\<close>
                by blast              
            qed
            ultimately have \<open>Suc k \<le> multiplicity p (fst (quotient_of (u + v)))\<close>
              using multiplicity_geI[where p = p and x = "fst (quotient_of (u + v))" 
                  and n = "Suc k"]
              by auto
            thus ?thesis
              using \<open>fst (quotient_of (u + v)) = p ^ k * m\<close> Suc_n_not_le_n k_def 
              by blast
          qed
          define w where \<open>w = Fract m (snd (quotient_of (u + v)))\<close>
          hence \<open>u + v = (p ^ k) * w\<close> 
          proof-
            have \<open>u + v = Fract (fst (quotient_of (u + v))) (snd (quotient_of (u + v)))\<close>
              unfolding quotient_of_def
              by (smt quotient_of_unique theI')             
            also have \<open>\<dots> = Fract ((p ^ k) * m) (snd (quotient_of (u + v)))\<close>
              by (simp add: \<open>fst (quotient_of (u + v)) = int (p ^ k) * m\<close>)            
            also have \<open>\<dots> = (Fract (p ^ k) 1) 
                        * (Fract m (snd (quotient_of (u + v))))\<close>
              by simp            
            also have \<open>\<dots> = (p ^ k) *  Fract m (snd (quotient_of (u + v)))\<close>
            proof-
              have \<open>(Fract (p ^ k) 1) = p ^ k\<close>
                by (metis Fract_of_nat_eq of_rat_of_nat_eq)              
              thus ?thesis
                by (metis of_rat_mult)               
            qed
            finally show ?thesis
              unfolding w_def
              by auto
          qed
          moreover have \<open>pnorm p w = 1\<close>
          proof-
            have \<open>\<not> (p dvd fst (quotient_of w))\<close>
              unfolding w_def
              by (metis \<open>\<not> int p dvd m\<close> \<open>\<not> int p dvd snd (quotient_of (u + v))\<close> dvd_0_right dvd_def
                  dvd_mult_left fst_quotient_of_divide)               
            moreover have \<open>\<not> (p dvd snd (quotient_of w))\<close>
              unfolding w_def
              using \<open>\<not> (p dvd snd (quotient_of (u+v)))\<close> dvd_trans snd_quotient_of_divide 
              by blast
            ultimately have \<open>pval p w = 0\<close>
              by (metis assms pval_unit_dvd_D pval_zero)              
            moreover have \<open>w \<noteq> 0\<close>
            proof(rule classical)
              assume \<open>\<not> (w \<noteq> 0)\<close>
              hence \<open>w = (0::real)\<close>
                by auto
              hence \<open>u + v = (p ^ k) * (0::real)\<close>
                by (simp add: \<open>of_rat (u + v) = of_nat (p ^ k) * of_rat w\<close>)
              also have \<open>\<dots> = 0\<close>
                by simp
              finally have \<open>u + v = 0\<close>
                by simp
              thus ?thesis
                using \<open>u + v \<noteq> 0\<close>
                by blast
            qed
            ultimately show ?thesis
              using assms pnorm_pval_zero 
              by blast               
          qed
          ultimately show ?thesis 
            by blast
        qed
        then obtain k::nat and w::rat where \<open>u + v = (p ^ k) * w\<close> and \<open>pnorm p w = 1\<close>
          by blast
        have \<open>x + y = (p powr (pval p x)) * (p ^ k) * w\<close>
          using \<open>x + y = (p powr (pval p x)) * (u + v)\<close>  \<open>u + v = (p ^ k) * w\<close>
          by simp
        also have \<open>\<dots> = (p powr (pval p x + k)) * w\<close>
        proof-
          have \<open>(p powr (pval p x)) * (p ^ k) = p powr (pval p x + k)\<close>
          proof-
            have \<open>(p powr (pval p x)) * (p ^ k) = (p powr (pval p x)) * (p powr k)\<close>
            proof-
              have \<open>p powr k = p ^ k\<close>
                by (simp add: assms powr_realpow prime_gt_0_nat)              
              thus ?thesis
                by simp
            qed
            also have \<open>\<dots> = p powr (pval p x + k)\<close>
            proof-
              have \<open>p > 1\<close>
                using \<open>prime p\<close> prime_gt_1_nat 
                by auto
              thus ?thesis
                by (simp add: powr_add) 
            qed
            finally show ?thesis
              by simp
          qed
          thus ?thesis 
            by simp
        qed
        finally have \<open>x + y = (p powr (pval p x + k)) * w\<close>
          by blast
        hence \<open>pval p (x + y) = pval p x + k\<close>
          using \<open>pnorm p w = 1\<close>
          by (smt assms pnorm_eq_zero_D pnorm_pval_zero pval_uniq)
        hence \<open>- pval p (x + y) \<le> - pval p x\<close>
          by auto
        have \<open>p powr (- pval p (x + y)) \<le> p powr (- pval p x)\<close>
        proof-
          have \<open>p > 1\<close>
            using \<open>prime p\<close> prime_gt_1_nat 
            by auto
          thus ?thesis 
            using \<open>- pval p (x + y) \<le> - pval p x\<close>
            by auto
        qed
        thus ?thesis
          using False \<open>pnorm p x = pnorm p y\<close> \<open>x \<noteq> 0\<close> pnorm_simplified 
          by auto
      qed
    qed
  } note eq = this

  {
    have \<open>pnorm p x < pnorm p y \<Longrightarrow> pnorm p (x + y) \<le> pnorm p y\<close>
      for x y
    proof(cases \<open>x = 0\<close>)
      case True
      thus ?thesis
        by auto
    next
      case False
      assume \<open>pnorm p x < pnorm p y\<close>
      have \<open>x \<noteq> 0\<close> 
        using False
        by blast
      hence \<open>\<exists> u::rat. x = (p powr (pval p x)) * u \<and> pnorm p u = 1\<close>
        by (simp add: assms pnorm_decomposition)
      then obtain u::rat where \<open>x = (p powr (pval p x)) * u\<close> and \<open>pnorm p u = 1\<close>
        by blast
      have \<open>y \<noteq> 0\<close> 
        using False
        by (smt \<open>pnorm p x < pnorm p y\<close> assms pnorm_eq_zero_D pnorm_geq_zero)        
      hence \<open>\<exists> v::rat. y = (p powr (pval p y)) * v \<and> pnorm p v = 1\<close>
        by (simp add: assms pnorm_decomposition)
      then obtain v::rat where \<open>y = (p powr (pval p y)) * v\<close> and \<open>pnorm p v = 1\<close>
        by blast
      have \<open>pval p x > pval p y\<close>
      proof-
        have \<open>pnorm p x = p powr (- pval p x)\<close>
          using \<open>x \<noteq> 0\<close>
          by (simp add: pnorm_simplified)
        moreover have \<open>pnorm p y = p powr (- pval p y)\<close>
          using \<open>y \<noteq> 0\<close>
          by (simp add: pnorm_simplified)
        moreover have \<open>p > 1\<close>
          using \<open>prime p\<close> prime_gt_1_nat 
          by auto
        ultimately have \<open>-pval p x < -pval p y\<close>
          using \<open>pnorm p x < pnorm p y\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
          by simp          
        thus ?thesis 
          by simp
      qed
      hence \<open>\<exists> l::nat. l = pval p x - pval p y\<close>
        by presburger
      then obtain l::nat where \<open>l = pval p x - pval p y\<close>
        by blast
      hence \<open>l \<ge> 1\<close>
        using \<open>pval p x > pval p y\<close>
        by linarith
      define w::rat where \<open>w = ((of_nat p) ^ l) * u + v\<close>
      have \<open>pnorm p w = 1\<close>
      proof-
        have \<open>pnorm p (((of_nat p) ^ l) * u) < 1\<close>
        proof-
          have \<open>pnorm p ((of_nat p) ^ l) = 1/((of_nat p) ^ l)\<close>
            using \<open>prime p\<close> pnorm_primepow 
            by auto
          also have \<open>\<dots> < 1\<close>
          proof-
            have \<open>p > 1\<close>
              using \<open>prime p\<close> prime_gt_1_nat 
              by auto
            thus ?thesis
              using \<open>l \<ge> 1\<close>
              by auto 
          qed
          finally show ?thesis
            by (simp add: \<open>pnorm p u = 1\<close> assms pnorm_multiplicativity)            
        qed
        thus ?thesis
          using \<open>pnorm p v = 1\<close> \<open>prime p\<close>
          by (simp add: add.commute pnorm_unit_ball w_def)
      qed
      have \<open>x + y = (p powr (pval p x)) * u + (p powr (pval p y)) * v\<close>
        by (simp add: \<open>of_rat x = complex_of_real (real p powr real_of_int (pval p x)) * of_rat u\<close> 
            \<open>of_rat y = complex_of_real (real p powr real_of_int (pval p y)) * of_rat v\<close> of_rat_add)
      also have \<open>\<dots> = (p powr (pval p y)) * (p powr (pval p x - pval p y)) * u
                    + (p powr (pval p y)) * v\<close>
      proof-
        have \<open>(p powr (pval p y)) * (p powr (pval p x - pval p y)) 
            = p powr ( (pval p y) + (pval p x - pval p y) )\<close>
          using Transcendental.powr_add[where x = p and a = "pval p y" and b = "pval p x - pval p y"]
          by simp
        also have \<open>\<dots> = p powr (pval p x)\<close>
        proof-
          have \<open>(pval p y) + (pval p x - pval p y) = pval p x\<close>
            by simp
          thus ?thesis 
            by simp
        qed
        finally have \<open>(p powr (pval p y)) * (p powr (pval p x - pval p y)) = p powr (pval p x)\<close>
          by blast
        thus ?thesis
          by simp
      qed
      also have \<open>\<dots> = (p powr (pval p y)) * ( (p powr (pval p x - pval p y)) * u + v)\<close>
        by (simp add: linordered_field_class.sign_simps(18))
      also have \<open>\<dots> = (p powr (pval p y)) * ( (p powr l) * u + v)\<close>
        using \<open>l = pval p x - pval p y\<close>
        by (metis of_int_of_nat_eq)
      also have \<open>\<dots> = (p powr (pval p y)) * ( (p ^ l) * u + v)\<close>
      proof-
        have \<open>p > 1\<close>
          using \<open>prime p\<close> prime_gt_1_nat 
          by auto
        hence \<open>p powr l = p ^ l\<close>
          by (simp add: powr_realpow)          
        thus ?thesis 
          by simp
      qed
      also have \<open>\<dots> = (p powr (pval p y)) * w\<close>
        unfolding w_def
        by (metis (no_types, lifting) of_nat_power of_rat_add of_rat_mult of_rat_of_nat_eq)
      finally have \<open>x + y = (p powr (pval p y)) * w\<close>
        by blast
      hence \<open>pval p (x + y) = pval p y\<close>
        by (metis \<open>pnorm p w = 1\<close> assms pnorm_eq_zero_D pnorm_pval_zero_D pval_uniq zero_neq_one)
      hence \<open>pnorm p (x + y) = pnorm p y\<close>
      proof(cases \<open>x + y = 0\<close>)
        case True
        hence \<open>x = - y\<close>
          by simp
        hence \<open>pnorm p x = pnorm p (-y)\<close>
          by simp
        thus ?thesis
          using \<open>pnorm p x < pnorm p y\<close>
          by (metis True \<open>pval p (x + y) = pval p y\<close> add.commute assms pnorm_pval_zero
              pnorm_unit_ball pval_zero)                     
      next
        case False
        thus ?thesis 
          using \<open>y \<noteq> 0\<close>
          using \<open>pval p (x + y) = pval p y\<close> pval_pnorm 
          by blast
      qed
      thus \<open>pnorm p (x + y) \<le> pnorm p y\<close>
        by auto
    qed  } note less = this

  show ?thesis
  proof(cases \<open>pnorm p x \<le> pnorm p y\<close>)
    case True
    thus ?thesis
    proof(cases \<open>pnorm p x = pnorm p y\<close>)
      case True
      thus ?thesis
        using eq
        by simp
    next
      case False
      hence \<open>pnorm p x < pnorm p y\<close>
        using \<open>pnorm p x \<le> pnorm p y\<close>
        by auto
      thus ?thesis
        using less
        by fastforce           
    qed
  next
    case False
    hence \<open>pnorm p y < pnorm p x\<close>
      by simp
    thus ?thesis
      using less add.commute
      by smt
  qed
qed

lemma pnorm_ultrametric_sum:
  fixes p::nat and A::\<open>nat set\<close> and x::\<open>nat \<Rightarrow> rat\<close>
  assumes \<open>prime p\<close>
  shows \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> pnorm p (sum x A) \<le> Max ((\<lambda> i. pnorm p (x i)) ` A)\<close>
proof-
  {  have \<open>\<And> A. card A = Suc n \<Longrightarrow> pnorm p (sum x A) \<le> Max ((\<lambda> i. pnorm p (x i)) ` A)\<close>
      for n
    proof(induction n)
      case 0
      hence \<open>\<exists> a. A = {a}\<close>
        by (metis One_nat_def card_1_singletonE)
      then obtain a where \<open>A = {a}\<close>
        by blast
      have \<open>pnorm p (sum x {a}) = pnorm p (x a)\<close>
        by simp        
      moreover have \<open>(MAX i\<in>{a}. pnorm p (x i)) = pnorm p (x a)\<close>
        by simp        
      ultimately show ?case
        by (simp add: \<open>A = {a}\<close>)
    next
      case (Suc n)
      have \<open>card A = Suc (Suc n)\<close>
        by (simp add: Suc.prems)
      hence \<open>\<exists> a A'. A = insert a A' \<and> a \<notin> A'\<close>
      proof -
        have "\<And>n. card ({}::nat set) \<noteq> Suc n"
          by (metis card_atMost card_subset_eq empty_subsetI finite_atMost 
              not_empty_eq_Iic_eq_empty)
        thus ?thesis
          by (metis (no_types) Diff_iff Suc.prems all_not_in_conv insertI1 insert_Diff_single
              insert_absorb)
      qed        
      then obtain a A' where \<open>A = insert a A'\<close> and \<open>a \<notin> A'\<close>
        by blast
      hence \<open>card A' = Suc n\<close>
        using \<open>card A = Suc (Suc n)\<close>
        by (metis card_insert_if card_le_Suc_iff finite_insert le_refl nat.inject)
      have \<open>finite A'\<close>
        using \<open>card A' = Suc n\<close> card_infinite 
        by fastforce
      have \<open>sum x A =  x a + (sum x A')\<close>
        using Groups_Big.comm_monoid_add_class.sum.insert_remove[where A = A and x = "a" 
            and g = "x"] \<open>A = insert a A'\<close> \<open>a \<notin> A'\<close>
        by (simp add: \<open>finite A'\<close>) 
      hence \<open>pnorm p (sum x A) = pnorm p (x a + (sum x A'))\<close>
        by simp
      also have \<open>\<dots> \<le> max (pnorm p (x a)) (pnorm p (sum x A'))\<close>
        by (simp add: assms pnorm_ultrametric)
      also have \<open>\<dots> \<le> Max ((\<lambda> i. pnorm p (x i)) ` A)\<close>
      proof-
        have \<open>(\<lambda> i. pnorm p (x i)) ` A = insert (pnorm p (x a)) ((\<lambda> i. pnorm p (x i)) ` A')\<close>
          using  \<open>A = insert a A'\<close> \<open>a \<notin> A'\<close>
          by simp
        hence \<open>Max ((\<lambda> i. pnorm p (x i)) ` A) = 
               Max (insert (pnorm p (x a)) ((\<lambda> i. pnorm p (x i)) ` A'))\<close>
          by auto
        also have \<open>\<dots> = max (pnorm p (x a)) (Max ((\<lambda> i. pnorm p (x i)) ` A'))\<close>
        proof-
          have \<open>finite ((\<lambda>i. pnorm p (x i)) ` A')\<close>
            using \<open>finite A'\<close>
            by blast
          moreover have \<open>((\<lambda>i. pnorm p (x i)) ` A') \<noteq> {}\<close>
          proof-
            have \<open>A' \<noteq> {}\<close>
              using \<open>card A' = Suc n\<close>
              by auto
            thus ?thesis
              by simp
          qed
          ultimately show ?thesis 
            using Lattices_Big.linorder_class.Max_insert[where A = "((\<lambda> i. pnorm p (x i)) ` A')" 
                and x = "pnorm p (x a)"] 
            by blast
        qed
        finally show ?thesis
          using Suc.IH \<open>card A' = Suc n\<close> 
          by fastforce 
      qed
      finally show \<open>pnorm p (sum x A) \<le> Max ((\<lambda> i. pnorm p (x i)) ` A)\<close> 
        by blast
    qed
  } note 1 = this
  assume \<open>finite A\<close> and \<open>A \<noteq> {}\<close>
  hence \<open>\<exists> n. card A = Suc n\<close>
    by (metis card.insert_remove finite.cases)
  then obtain n where \<open>card A = Suc n\<close>
    by blast
  thus ?thesis
    using 1 
    by blast
qed


end