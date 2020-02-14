(*
  File:    Harmonic_2_adic.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
  Author:  Manuel Eberl, TU München
*)
section \<open>Applications of the p-adic norm to the harmonic numbers\<close>
theory Harmonic_2_adic

imports 
  "HOL-Analysis.Harmonic_Numbers"
  Pnorm

begin

text \<open>
 In 1915, L. Theisinger ~\cite{theisinger1915bemerkung} proved that, for \<^term>\<open>(n::nat) \<ge> 2\<close>, the
 harmonic number \<^term>\<open>(harm n) :: real\<close> is not an integer. In 1918,  J. K{\"u}rsch{\'a}k  
 ~\cite{kurschak1918harmonic} proved that, for \<^term>\<open>(n::nat)+2 \<ge> (m::nat)\<close>, the difference between 
 the two harmonic numbers \<^term>\<open>((harm n) - (harm m))::real\<close> is not an integer. We formalize these 
 results as theorems @{text Taeisinger} and @{text Kurschak}, respectively. The proofs will be
 simple consequences the computation of the 2-adic norm of the harmonic numbers 
 (lemma @{text harmonic_numbers_2norm}).
\<close>

subsection \<open>Auxiliary results\<close>
text\<open>
  The following function is a variation of \<^term>\<open>harm\<close>, where the codomain is typ>\<open>rat\<close>. We need this
  function because the codomain of \<^term>\<open>harm\<close> cannot be \<^typ>\<open>rat\<close>.
\<close>
fun Harm :: "nat \<Rightarrow> rat" where
  "Harm 0 = 0" |
  "Harm (Suc n) = Harm n + inverse (of_nat (Suc n))"

lemma Harm'[simp]: "real_of_rat (Harm n) = harm n"
proof(induction n)
  case 0 thus ?case by (simp add: harm_expand(1)) 
next
  case (Suc n)
  have "real_of_rat (Harm (Suc n)) = real_of_rat (Harm n + inverse (of_nat (Suc n)))"
    by simp
  also have "\<dots> = real_of_rat (Harm n) + real_of_rat (inverse (of_nat (Suc n)))"
    by (simp add: of_rat_add)
  also have "\<dots> = harm n + real_of_rat (inverse (of_nat (Suc n)))"
    by (simp add: Suc.IH)    
  finally show ?case
    by (metis harm_Suc of_rat_inverse of_rat_of_nat_eq) 
qed

lemma harm_diff_plus:
  "harm (n+t) - harm n = (\<Sum>k=n+1..n+t. inverse (of_nat k))"
proof(induct t)
  case 0 thus ?case by simp 
next
  case (Suc t) show ?case
  proof -
    have f1: "\<forall>a b c. (a::'a) + b \<noteq> a + c \<or> b = c"
      by (meson add_left_imp_eq)
    have f2: "(\<Sum>n = 1..n. inverse (of_nat n::'a)) + (harm (n + Suc t) - harm n) 
            = (\<Sum>n = 1..n + Suc t. inverse (of_nat n))"
      by (metis (no_types) add.commute diff_add_cancel harm_def)
    have "(\<Sum>n = 1..n + Suc t. inverse (of_nat n::'a)) 
        = (\<Sum>n = 1..n. inverse (of_nat n)) + (\<Sum>n = n + 1..n + Suc t. inverse (of_nat n))"
      by (meson le_add2 sum.ub_add_nat)
    thus ?thesis
      using f2 f1 by presburger
  qed 
qed

lemma harm_diff:
  "n \<ge> m \<Longrightarrow> harm n - harm m = (\<Sum>k=m+1..n. inverse (of_nat k))"
  using harm_diff_plus[where n = m and t = "n - m"] by simp

lemma harm_diff':
  "n \<ge> m \<Longrightarrow> Harm n - Harm m = (\<Sum>k=m+1..n. inverse (rat_of_nat k))"
proof-
  assume "n \<ge> m"
  have "real_of_rat (Harm n - Harm m) = harm n - harm m"
    by (simp add: of_rat_diff)
  also have "\<dots> = (\<Sum>k=m+1..n. inverse (of_nat k))"
    using harm_diff \<open>m \<le> n\<close> by blast 
  also have "\<dots> = (\<Sum>k=m+1..n. real_of_rat (inverse (rat_of_nat k)))"
    by (simp add: of_rat_inverse)
  also have "\<dots> = real_of_rat (\<Sum>k=m+1..n. (inverse (rat_of_nat k)))"
    by (simp add: of_rat_sum)
  finally show ?thesis by auto
qed

lemma Harm_explicit:
  "Harm n = (\<Sum>k=1..n. inverse (rat_of_nat k))"
  using harm_diff' by fastforce

lemma Harm_incre: \<open>m < n \<Longrightarrow> Harm m < Harm n\<close>
proof-
  assume \<open>m < n\<close>
  have \<open>finite {m + 1..n}\<close>
    by simp
  moreover have \<open>{m + 1..n} \<noteq> {}\<close>
    using \<open>m < n\<close>
    by simp
  moreover have \<open>k \<in> {m + 1..n} \<Longrightarrow> 0 < inverse (rat_of_nat k)\<close> for k
  proof-
    assume \<open>k \<in> {m + 1..n}\<close>
    hence \<open>k \<ge> 1\<close>
      by auto
    thus ?thesis
      by (simp add: zero_less_Fract_iff) 
  qed
  ultimately have \<open>0 < (\<Sum>k = m + 1..n. inverse (rat_of_nat k))\<close>
    using Groups_Big.ordered_comm_monoid_add_class.sum_pos[where I = "{m+1..n}" 
        and f = "\<lambda> k. inverse (rat_of_nat k)"] by auto
  thus ?thesis
    using harm_diff'[where n = n and m = m] \<open>n > m\<close> 
    by simp
qed

lemma Harm_diff_less_1:
  "m < n \<Longrightarrow> n \<le> 2*m \<Longrightarrow> Harm n - Harm m < 1"
proof-
  assume "m < n" and "n \<le> 2*m"
  have \<open>(\<Sum>k = m + 1..n. inverse (rat_of_nat k)) < 1\<close>
  proof-
    have \<open>finite {m + 1..n}\<close>
      by simp
    moreover have \<open>{m + 1..n} \<noteq> {}\<close>
      using \<open>m < n\<close> by simp
    moreover have \<open>k \<in> {m + 1..n} \<Longrightarrow> inverse (rat_of_nat k) \<le> inverse (rat_of_nat (m+1))\<close> for k
    proof-
      assume \<open>k \<in> {m + 1..n}\<close>
      have \<open>k \<ge> m+1\<close>
        using \<open>k \<in> {m + 1..n}\<close>
        by auto
      thus ?thesis
        by auto
    qed
    ultimately have \<open>(\<Sum>k = m + 1..n. inverse (rat_of_nat k)) 
                     \<le> of_nat (card {m + 1..n}) * inverse (rat_of_nat (m+1))\<close>
      using Groups_Big.sum_bounded_above[where A = "{m+1..n}" and K = "inverse (rat_of_nat (m+1))"
          and f = "\<lambda> k. inverse (rat_of_nat k)"]
      by auto
    also  have \<open>\<dots> \<le> of_nat m * inverse (rat_of_nat (m+1))\<close>
    proof-
      have \<open>card {m+1..n} \<le> m\<close>
      proof-
        have \<open>card {m+1..n} = n - m\<close>
          by auto
        thus ?thesis
          using \<open>n \<le> 2*m\<close> by simp
      qed
      moreover have \<open>card  {m + 1..n} > 0\<close>
        using \<open>{m + 1..n} \<noteq> {}\<close> card_gt_0_iff by blast
      ultimately show ?thesis by simp
    qed
    also have \<open>\<dots> < 1\<close>
    proof -
      have f1: "0 < Fract 1 (int (m + 1))"
        using zero_less_Fract_iff by auto
      have "rat_of_nat (m + 1) * inverse (rat_of_nat (m + 1)) = 1"
        by auto
      thus ?thesis
        using f1 by (metis (no_types) Fract_of_nat_eq inverse_rat less_add_same_cancel1 less_one 
            linordered_field_class.sign_simps(35) linordered_field_class.sign_simps(44) 
            of_nat_0_less_iff of_nat_add)
    qed       
    finally show ?thesis
      by blast
  qed
  thus ?thesis
    using harm_diff' \<open>m < n\<close> by auto
qed

(* TODO: delete *)
lemma sum_last:
  fixes n::nat and a::\<open>nat \<Rightarrow> rat\<close>
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum>k = 1..n - 1. (a k)) + (a n) = (\<Sum>k = 1..n. (a k))\<close>
  using \<open>n \<ge> 2\<close>
  apply auto
  by (smt add.commute add_leD2 le_add_diff_inverse numeral_1_eq_Suc_0 numeral_2_eq_2 
      numeral_One plus_1_eq_Suc sum.nat_ivl_Suc')

lemma harmonic_numbers_2norm:
  fixes n::nat and r::rat
  assumes "n \<ge> 1"
  shows "pnorm 2 (Harm n) = 2^(nat(\<lfloor>log 2 n\<rfloor>))"
proof(cases \<open>n = 1\<close>)
  case True
  have \<open>prime (2::nat)\<close>
    by simp
  hence \<open>Harm 1 = 1\<close>
    by (simp add: One_rat_def)
  hence \<open>pnorm 2 (Harm 1) = pnorm 2 1\<close>
    by simp
  also have \<open>\<dots> = 1\<close>
    by simp
  also have \<open>\<dots> = 2^(nat(\<lfloor>log 2 1\<rfloor>))\<close>
  proof-
    have \<open>\<lfloor>log 2 1\<rfloor> = 0\<close>
      by simp      
    thus ?thesis
      by auto
  qed
  finally show ?thesis
    using \<open>n = 1\<close>
    by auto
next
  case False
  hence \<open>n \<ge> 2\<close>
    using \<open>n \<ge> 1\<close>
    by auto
  define l where \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close>
    (*
  define H where \<open>H = (\<Sum>k = 1..n. (inverse  (of_nat k)))\<close>
*)
  have \<open>prime (2::nat)\<close>
    by simp
  have \<open>l \<ge> 1\<close>
  proof-
    have \<open>log 2 n \<ge> 1\<close>
      using \<open>n \<ge> 2\<close>
      by auto
    hence \<open>\<lfloor>log 2 n\<rfloor> \<ge> 1\<close>
      by simp
    thus ?thesis 
      using \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close> \<open>1 \<le> \<lfloor>log 2 (real n)\<rfloor>\<close> \<open>l = nat \<lfloor>log 2 (real n)\<rfloor>\<close> nat_mono 
      by presburger            
  qed
  hence \<open>(2::nat)^l \<ge> 2\<close>
  proof -
    have "(2::nat) ^ 1 \<le> 2 ^ l"
      by (metis \<open>1 \<le> l\<close> one_le_numeral power_increasing)
    thus ?thesis
      by (metis semiring_normalization_rules(33))
  qed
  have \<open>pnorm 2 ((2^l) * Harm n) = 1\<close>
  proof-
    define pre_H where \<open>pre_H = (\<Sum>k = 1..(2^l-1). inverse (rat_of_nat k))\<close>
    define post_H where \<open>post_H = (\<Sum>k = (2^l+1)..n. inverse (rat_of_nat k))\<close>
    have \<open>Harm n = pre_H + (inverse  (of_nat (2^l))) + post_H\<close>
    proof-
      have \<open>pre_H + (inverse  (of_nat (2^l))) = (\<Sum>k = 1..(2^l-1). inverse (rat_of_nat k)) 
                  + (inverse  (of_nat (2^l)))\<close>
        unfolding pre_H_def
        by auto
      also have \<open>\<dots> = (\<Sum>k = 1..2^l. inverse (rat_of_nat k))\<close>
        by (metis  \<open>2 \<le> 2 ^ l\<close>  sum_last)
      finally have \<open>pre_H + inverse (rat_of_nat (2^l)) = (\<Sum>k = 1..2 ^ l. inverse (rat_of_nat k))\<close>
        by auto 
      moreover have \<open>(\<Sum>k = 1..2 ^ l. inverse (rat_of_nat k)) + post_H = Harm n\<close>
      proof-
        have \<open>(\<Sum>k = 1..2 ^ l. inverse (rat_of_nat k)) + post_H
              = (\<Sum>k = 1..2 ^ l. inverse (rat_of_nat k)) +
                (\<Sum>k = 2 ^ l + 1..n. inverse (rat_of_nat k))\<close>
          unfolding post_H_def
          by blast
        also have \<open>\<dots>  = (\<Sum>k = 1..n. inverse (rat_of_nat k))\<close>
        proof-
          have \<open>2 ^ l \<le> n\<close>
          proof-
            have \<open>2 ^ l =  2 ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
              unfolding l_def
              by simp
            also have \<open>\<dots> =  2 powi (nat \<lfloor>log 2 (real n)\<rfloor>)\<close>
              by (metis intpow_int)                           
            also have \<open>\<dots> \<le>  2 powr (log 2 (real n))\<close>
            proof-
              have \<open>\<lfloor>log 2 (real n)\<rfloor> \<le> log 2 (real n)\<close>
                by simp
              moreover have \<open>(2::real) > 1\<close>
                by simp
              ultimately show ?thesis 
                using Transcendental.powr_le_cancel_iff[where x = 2 and a = "\<lfloor>log 2 (real n)\<rfloor>" 
                    and b = "log 2 (real n)"] assms unfolding intpow_def 
                by (simp add: powr_real_of_int)
            qed
            also have \<open>\<dots> = n\<close>
            proof-
              have \<open>(2::real) > 1\<close>
                by simp                
              moreover have \<open>n > 0\<close>
                using \<open>n \<ge> 2\<close>
                by auto
              ultimately show ?thesis
                by simp
            qed
            finally show ?thesis 
              by simp
          qed
          thus ?thesis
            by (metis le_add2 le_add_diff_inverse sum.ub_add_nat)
        qed
        finally have \<open>(\<Sum>k = 1..2 ^ l. inverse (rat_of_nat k)) + post_H = 
            (\<Sum>k = 1..n.  inverse (rat_of_nat k))\<close>
          by auto
        thus ?thesis
          unfolding pre_H_def
          using Harm_explicit by auto
      qed
      ultimately show ?thesis
        by linarith
    qed
    moreover have \<open>pnorm 2 ((2^l) * (inverse  (of_nat (2^l)))) = 1\<close>
    proof-
      have \<open>(2::nat)^l \<noteq> 0\<close>
        by auto
      hence \<open>((2::nat)^l) * (inverse  (of_nat ((2::nat)^l))) = 1\<close>
      proof -
        have "int (2 ^ l) \<noteq> 0"
          using \<open>2 ^ l \<noteq> 0\<close> by linarith
        hence "1 = Fract (int (2 ^ l) * 1) (int (2 ^ l) * 1)"
          by (metis (no_types) One_rat_def mult_rat_cancel)
        thus ?thesis
          by simp
      qed        
      hence \<open>pnorm 2 (((2::rat)^l) * (inverse  (of_nat ((2::nat)^l)))) = pnorm 2 1\<close>
        by simp
      also have \<open>\<dots> = 1\<close>
        by simp
      finally show ?thesis 
        by blast
    qed
    moreover have \<open>pnorm 2 ((2^l) * pre_H) < 1\<close>
    proof-
      have \<open>(2^l) * pre_H = (\<Sum>k = 1..2 ^ l - 1. (2^l) * inverse (rat_of_nat k) )\<close>
        unfolding pre_H_def
        using Groups_Big.semiring_0_class.sum_distrib_left[where r = \<open>2^l\<close> 
            and f = \<open>(\<lambda> k. inverse (rat_of_nat k))\<close> and A = \<open>{1..(2^l - 1)}\<close>]
        by auto
      hence \<open>pnorm 2 (2 ^ l * pre_H) =
              pnorm 2 (\<Sum>k = 1..2 ^ l - 1. (2 ^ l) * inverse (rat_of_nat k))\<close>
        by simp
      also have \<open>\<dots> \<le>
              Max ((\<lambda> k. pnorm 2 ((2 ^ l) * inverse (rat_of_nat k)))`{1..2^l-1})\<close>
      proof-
        have \<open>pnorm 2 (\<Sum>k = 1..2 ^ l - 1.  (2 ^ l) * inverse (rat_of_nat k))
           = pnorm 2 (sum (\<lambda> k.  (2 ^ l) * inverse (rat_of_nat k)) {1..(2::nat)^l-1})\<close>
          by blast
        also have \<open>\<dots> \<le> Max ((\<lambda> k. pnorm 2 ((2 ^ l) * inverse (rat_of_nat k) ))`{1..2^l-1})\<close>
          using \<open>prime 2\<close>  pnorm_sum_le[where p = 2 and A = \<open>{1..2^l-1}\<close> 
              and x = \<open>(\<lambda> k. (2 ^ l) * inverse (rat_of_nat k))\<close>]
          by (metis Nat.le_diff_conv2 \<open>2 \<le> 2 ^ l\<close> add_leD1 atLeastatMost_empty_iff2 
              finite_atLeastAtMost nat_1_add_1)          
        finally show ?thesis
          using \<open>pnorm 2 (\<Sum>k = 1..2 ^ l - 1. 2 ^ l * inverse (rat_of_nat k)) 
            \<le> (MAX k\<in>{1..2 ^ l - 1}. pnorm 2 (2 ^ l * inverse (rat_of_nat k)))\<close> by blast          
      qed
      also have \<open>\<dots> < 1\<close>
      proof-
        have \<open>finite ((\<lambda> k. pnorm 2 (2 ^ l) * inverse (rat_of_nat k))`{1..2^l-1})\<close>
          by blast          
        moreover have \<open>((\<lambda> k. pnorm 2 ((2 ^ l) * inverse (rat_of_nat k)))`{1..2^l-1}) \<noteq> {}\<close>
        proof-
          have \<open>(1::nat) \<le> (2::nat)^l-1\<close>
            using \<open>(2::nat)^l \<ge> 2\<close>
            by auto
          hence \<open>{(1::nat)..(2::nat)^l-1} \<noteq> {}\<close>
            using Set_Interval.order_class.atLeastatMost_empty_iff2[where a = "1::nat" 
                and b = "(2::nat)^l - 1"]
            by auto
          thus ?thesis
            by blast
        qed
        moreover have \<open>x \<in> ((\<lambda> k. pnorm 2 ((2 ^ l) * inverse (rat_of_nat k)))`{1..2^l-1}) \<Longrightarrow> x < 1\<close>
          for x
        proof-
          assume \<open>x \<in> ((\<lambda> k. pnorm 2 ((2 ^ l) * inverse (rat_of_nat k)))`{1..2^l-1})\<close>
          then obtain k where \<open>x = pnorm 2 ((2 ^ l) * inverse (rat_of_nat k))\<close> and \<open>k \<in> {1..2^l-1}\<close>
            by blast
          have \<open>pnorm 2 ((2 ^ l) * inverse (rat_of_nat k)) < 1\<close>
          proof-
            have \<open>pnorm 2 ((2::rat)^l) = 1/(2::nat)^l\<close>
              using  \<open>prime (2::nat)\<close> pnorm_primepow[where p = "(2::nat)"]
              by auto
            moreover have \<open>pnorm 2 (inverse (rat_of_nat k)) < (2::nat)^l\<close>
            proof-
              have \<open>2 powi (- pval 2 (inverse (rat_of_nat k))) < (2::nat)^l\<close>
              proof-
                have \<open>pval 2 (Fract k 1) < l\<close>
                proof-
                  have \<open>pval 2 (Fract k 1) = multiplicity (2::int) k\<close>
                    by (smt Fract_of_nat_eq Suc_1 multiplicity_int_int of_nat_1 of_nat_Suc 
                        pval_of_nat)
                  also have \<open>\<dots> < l\<close>
                  proof(rule classical)
                    assume \<open>\<not>(multiplicity 2 (int k) < int l)\<close>
                    hence \<open>multiplicity 2 (int k) \<ge> int l\<close>
                      by simp
                    hence \<open>((2::nat)^l) dvd k\<close>
                      by (metis (full_types) int_dvd_int_iff multiplicity_dvd' of_nat_numeral
                          of_nat_power zle_int)
                    hence \<open>(2::nat)^l \<le> k\<close>
                      using \<open>k \<in> {1..2 ^ l - 1}\<close> dvd_nat_bounds
                      by auto
                    moreover have \<open>k < (2::nat)^l\<close>
                      using  \<open>k\<in>{1..(2::nat)^l - 1}\<close>
                      by auto                        
                    ultimately show ?thesis
                      by linarith 
                  qed
                  finally show ?thesis
                    by blast
                qed
                hence \<open>- pval 2 (inverse (rat_of_int k)) < l\<close>
                  using \<open>prime 2\<close> pval_inverse[where p = "2" and x = \<open>inverse (rat_of_int k)\<close>] 
                    Fract_of_int_quotient 
                  by auto
                hence \<open>2 powr (- pval 2 (inverse (rat_of_int k))) < 2 powr l\<close>
                  by auto
                also have \<open>\<dots> = (2::nat)^l\<close>
                proof -
                  have f1: "\<not> 2 \<le> (1::real)"
                    by auto
                  have f2: "\<forall>x1. ((1::real) < x1) = (\<not> x1 \<le> 1)"
                    by force
                  have "real (2 ^ l) = 2 ^ l"
                    by simp
                  hence "real l = log 2 (real (2 ^ l))"
                    using f2 f1 by (meson log_of_power_eq)
                  thus ?thesis
                    by simp
                qed
                finally show ?thesis 
                  unfolding intpow_def
                  using of_int_of_nat_eq power_inverse powr_real_of_int 
                    \<open>- pval 2 (inverse (rat_of_int (int k))) < int l\<close> by auto 
              qed
              moreover have \<open>pnorm 2 (inverse (rat_of_nat k)) = 2 powi (- pval 2 (inverse (rat_of_nat k)))\<close>
              proof-
                have \<open>k \<noteq> 0\<close>
                  using \<open>k\<in>{1..2^l - 1}\<close>
                  by simp
                hence \<open>inverse (rat_of_int k) \<noteq> 0\<close>
                  by auto
                thus ?thesis
                  using \<open>prime 2\<close> \<open>k \<noteq> 0\<close>
                  unfolding pnorm_def intpow_def
                  apply auto
                  by (simp add: powr_realpow)                                   
              qed
              ultimately show ?thesis
                by auto                
            qed
            moreover have \<open>pnorm 2 ((2::rat)^l) > 0\<close>
            proof-
              have \<open>(2::rat)^l \<noteq> 0\<close>
                by simp                  
              moreover have \<open>pnorm 2 ((2::rat)^l) \<ge> 0\<close>
                by (simp add: pnorm_nonneg)
              ultimately show ?thesis
                by (simp add: less_eq_real_def)
            qed
            moreover have \<open>pnorm 2 (inverse (rat_of_nat k)) > 0\<close>
            proof-
              have \<open>inverse (rat_of_nat k) \<noteq> 0\<close>
                using \<open>k \<in> {1..2^l-1}\<close>
                by simp
              moreover have \<open>pnorm 2 (inverse (rat_of_nat k)) \<ge> 0\<close>                  
                using \<open>prime (2::nat)\<close>
                by (simp add: pnorm_nonneg)                  
              ultimately show ?thesis
                using  \<open>prime (2::nat)\<close>
                by (simp add: pnorm_pos)
            qed
            ultimately have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (inverse (rat_of_nat k))) 
                  < (1/(2::nat)^l)*((2::nat)^l)\<close>
              by simp
            also have \<open>\<dots> = 1\<close>
            proof-
              have \<open>(2::nat)^l \<noteq> 0\<close>
                by simp                  
              thus ?thesis
                by simp 
            qed
            finally have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (inverse (rat_of_nat k))) < 1\<close>
              by blast
            moreover have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (inverse (rat_of_nat k))) 
                  = pnorm 2 (2 ^ l * inverse (rat_of_nat k))\<close>
              using \<open>prime 2\<close>
              by simp
            ultimately show ?thesis
              by auto              
          qed
          thus ?thesis
            using \<open>x = pnorm 2 (2 ^ l * inverse (rat_of_nat k))\<close> by blast

        qed
        ultimately show ?thesis 
          using Lattices_Big.linorder_class.Max_less_iff
            [where A = "((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})"]
          by auto
      qed
      finally show \<open>pnorm 2 (2 ^ l * pre_H) < 1\<close>
        by blast
    qed
    ultimately have \<open>pnorm 2 ((2^l) * (inverse  (of_nat (2^l))) + (2^l) * pre_H) = 1\<close>
      using pnorm_unit_ball[where p = 2 and x = "(2^l) *  (inverse  (of_nat (2^l)))" and y = "(2^l) * pre_H"]
      by simp
    moreover have \<open>pnorm 2 ((2^l) * post_H) < 1\<close>
    proof(cases \<open>2^l + 1 \<le> n\<close>)
      case True
      have \<open>pnorm 2 ((2^l) * post_H) = pnorm 2 (\<Sum>k = 2 ^ l + 1..n.  (2 ^ l)*(inverse (rat_of_int k)))\<close>
      proof-
        have \<open>(2^l) * post_H = (\<Sum>k = 2 ^ l+1..n. (2 ^ l)*(inverse (rat_of_int k)))\<close>
          unfolding post_H_def
          using Groups_Big.semiring_0_class.sum_distrib_left[where r = \<open>2^l\<close> 
              and f = \<open>(\<lambda> k. inverse (rat_of_int k))\<close> and A = \<open>{2 ^ l+1..n}\<close>]
          by auto
        thus ?thesis
          by simp
      qed
      also have \<open>\<dots>
           = pnorm 2 (sum (\<lambda> k. (2 ^ l)*(inverse (rat_of_int k))) {2 ^ l + 1..n})\<close>
        by blast
      also have \<open>\<dots>
           \<le> Max ((\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n})\<close>
      proof-
        have \<open>finite {2 ^ l + 1..n}\<close>
          by simp          
        moreover have \<open>{2 ^ l + 1..n} \<noteq> {}\<close>
          using True 
          by auto          
        ultimately show ?thesis 
          using \<open>prime 2\<close>  pnorm_sum_le[where p = 2 and A = \<open>{2 ^ l + 1..n}\<close> 
              and x = \<open>(\<lambda> k. (2 ^ l)*(inverse (rat_of_int k)))\<close>]
          by auto
      qed
      finally have \<open>pnorm 2 ((2^l) * post_H) \<le> 
          Max ((\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n})\<close>
        using \<open>pnorm 2 (2 ^ l * post_H) 
            = pnorm 2 (\<Sum>k = 2 ^ l + 1..n. 2 ^ l * inverse (rat_of_int (int k)))\<close> 
          \<open>pnorm 2 (\<Sum>k = 2 ^ l + 1..n. 2 ^ l * inverse (rat_of_int (int k))) 
          \<le> (MAX k\<in>{2 ^ l + 1..n}. pnorm 2 (2 ^ l * inverse (rat_of_int (int k))))\<close> 
        by linarith        
      moreover have \<open>((\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n}) \<noteq> {}\<close>
        using True 
        by auto        
      moreover have \<open>finite ((\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n})\<close>
        by blast        
      moreover have \<open>x \<in> (\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n} \<Longrightarrow> x < 1\<close>
        for x
      proof-
        assume \<open>x \<in> (\<lambda> k. pnorm 2 ((2 ^ l)*(inverse (rat_of_int k)))) ` {2 ^ l + 1..n}\<close>
        then obtain t where \<open>t \<in> {2 ^ l + 1..n}\<close> and \<open>x = pnorm 2 ((2 ^ l)*(inverse (rat_of_nat t)))\<close>
          by auto
        have  \<open>x = (pnorm 2 (2 ^ l)) * (pnorm 2 (inverse (rat_of_nat t)))\<close>
          using \<open>prime 2\<close> \<open>x = pnorm 2 ((2 ^ l)*(inverse  (rat_of_nat t)))\<close> pnorm_mult by blast         
        moreover have \<open>pnorm 2 (2 ^ l) = 1/(2^l)\<close>
          using \<open>prime 2\<close> pval_primepow[where p = "2::nat"]
          by (metis of_int_numeral of_nat_numeral pnorm_primepow)          
        moreover have \<open>pnorm 2 (inverse  (rat_of_nat t)) < 2^l\<close>
        proof(rule classical)
          assume \<open>\<not> (pnorm 2 (inverse  (rat_of_nat t)) < 2^l)\<close>
          hence \<open>pnorm 2 (inverse  (rat_of_nat t)) \<ge> 2^l\<close>
            by auto
          moreover have \<open>2 powi l = 2^l\<close>
            by auto            
          ultimately have \<open>pnorm 2 (inverse  (rat_of_nat t)) \<ge> 2 powi l\<close>
            by auto
          moreover have \<open>pnorm 2 (inverse  (rat_of_nat t)) 
                          = 2 powi (-pval 2 (inverse  (rat_of_nat t)))\<close>
          proof-
            have \<open>t \<noteq> 0\<close>
              using \<open>t \<in> {2^l + 1 .. n}\<close>
              by simp
            hence \<open>inverse (rat_of_nat t) \<noteq> 0\<close>
            proof -
              have "\<not> int t \<le> 0"
                by (metis \<open>t \<noteq> 0\<close> of_nat_le_0_iff)
              hence "\<not> inverse  (int t) \<le> 0"
                by (simp add: Fract_le_zero_iff)
              thus ?thesis
                by auto
            qed              
            thus ?thesis 
              unfolding intpow_def pnorm_def
              apply auto
              by (simp add: powr_realpow) 
          qed
          ultimately have \<open>-pval 2 (inverse  (rat_of_nat t)) \<ge> l\<close>
            by simp            
          hence \<open>-(multiplicity 2 (fst (quotient_of (inverse  (rat_of_nat t)))))
               + (multiplicity 2 (snd (quotient_of (inverse  (rat_of_nat t)))))
                     \<ge> l\<close>
            unfolding pval_def 
            by auto
          have \<open>quotient_of (inverse (rat_of_nat t)) = (1, t)\<close>
          proof-
            have \<open>inverse (rat_of_nat t) = Fract 1 t\<close>
              by (metis Fract_of_nat_eq inverse_rat)
            moreover have \<open>t > 0\<close>
              using \<open>t \<in> {2^l + 1 .. n}\<close>
              by simp
            moreover have \<open>coprime 1 t\<close>
              by simp
            ultimately show ?thesis
              by (simp add: quotient_of_Fract)             
          qed
          hence \<open>fst (quotient_of (inverse  (rat_of_nat t))) = 1\<close>
            by simp
          moreover have \<open>snd (quotient_of (inverse  (rat_of_nat t))) = t\<close>
          proof -
            have "Rat.normalize (1, int t) = quotient_of (inverse (rat_of_nat t))"
              by (metis (full_types) Fract_of_int_eq inverse_rat of_int_of_nat_eq quotient_of_Fract)
            hence "Rat.normalize (1, int t) = (1, snd (quotient_of (inverse (rat_of_nat t))))"
              by (metis calculation prod.exhaust_sel)
            thus ?thesis
              by (metis (full_types) Fract_of_int_eq inverse_rat normalize_eq of_int_eq_iff)
          qed            
          ultimately have \<open>- int(multiplicity (2::int) 1) + int(multiplicity (2::int) t) \<ge> l\<close>
            using \<open>-(multiplicity 2 (fst (quotient_of (inverse  (rat_of_nat t)))))
               + (multiplicity 2 (snd (quotient_of (inverse  (rat_of_nat t)))))
                     \<ge> l\<close>
            by auto
          moreover have \<open>multiplicity (2::int) 1 = 0\<close>
            by simp
          ultimately have \<open>multiplicity (2::int) t \<ge> l\<close>
            by auto
          hence \<open>2^l dvd t\<close>
            by (metis int_dvd_int_iff multiplicity_dvd' of_nat_numeral of_nat_power)
          hence \<open>\<exists> k::nat. 2^l * k = t\<close>
            by auto
          then obtain k::nat where \<open>2^l * k = t\<close>
            by blast
          have \<open>k \<ge> 2\<close>
          proof(rule classical)
            assume \<open>\<not>(k \<ge> 2)\<close>
            hence \<open>k < 2\<close>
              by simp
            moreover have \<open>k \<noteq> 0\<close>
            proof(rule classical)
              assume \<open>\<not>(k \<noteq> 0)\<close>
              hence \<open>k = 0\<close>
                by simp
              hence \<open>t = 0\<close>
                using \<open>2^l * k = t\<close>
                by auto
              thus ?thesis
                using \<open>t \<in> {2^l + 1 .. n}\<close>
                by auto
            qed
            moreover have \<open>k \<noteq> 1\<close>
            proof(rule classical)
              assume \<open>\<not>(k \<noteq> 1)\<close>
              hence \<open>k = 1\<close>
                by simp
              hence \<open>t = 2^l\<close>
                using \<open>2^l * k = t\<close>
                by auto
              thus ?thesis
                using \<open>t \<in> {2^l + 1 .. n}\<close>
                by auto
            qed
            ultimately show ?thesis
              by auto
          qed
          hence \<open>2^(Suc l) \<le> t\<close>
            using \<open>2 ^ l * k = t\<close> 
            by auto
          hence \<open>2^(Suc l) \<le> n\<close>
            using \<open>t \<in> {2^l + 1 .. n}\<close>
            by auto
          moreover have \<open>n < 2^(Suc l)\<close>
          proof -
            have f1: "\<forall>n na. (n \<le> na) = (int n + - 1 * int na \<le> 0)"
              by auto
            have f2: "int (Suc (nat \<lfloor>log 2 (real n)\<rfloor>)) + - 1 * int (Suc l) \<le> 0"
              by (simp add: l_def)
            have f3: "(- 1 * log 2 (real n) + real (Suc l) \<le> 0) = (0 \<le> log 2 (real n) + - 1 * real (Suc l))"
              by fastforce
            have f4: "real (Suc l) + - 1 * log 2 (real n) = - 1 * log 2 (real n) + real (Suc l)"
              by auto
            have f5: "\<forall>n na. \<not> 2 ^ n \<le> na \<or> real n + - 1 * log 2 (real na) \<le> 0"
              by (simp add: le_log2_of_power)
            have f6: "\<forall>x0 x1. (- 1 * int x0 + int (2 ^ x1) \<le> 0) = (0 \<le> int x0 + - 1 * int (2 ^ x1))"
              by auto
            have f7: "\<forall>x0 x1. int (2 ^ x1) + - 1 * int x0 = - 1 * int x0 + int (2 ^ x1)"
              by auto
            have "\<not> 0 \<le> log 2 (real n) + - 1 * real (Suc l)"
              using f2 by linarith
            then have "\<not> 0 \<le> int n + - 1 * int (2 ^ Suc l)"
              using f7 f6 f5 f4 f3 f1 by (metis (no_types))
            then show ?thesis
              by linarith
          qed                    
          ultimately show ?thesis
            by auto
        qed
        moreover have \<open>pnorm 2 (2 ^ l) \<ge> 0\<close>
          by (simp add: pnorm_nonneg)
        moreover have \<open>pnorm 2 (inverse  (rat_of_nat t)) \<ge> 0\<close>
          by (simp add: pnorm_nonneg)
        ultimately show ?thesis 
          by simp
      qed
      ultimately show ?thesis
        by (smt Max_in)
    next
      case False
      hence \<open>2 ^ l + 1 > n\<close>
        by simp
      hence \<open>{2 ^ l + 1..n} = {}\<close>
        by simp
      hence \<open>post_H = 0\<close>
        unfolding post_H_def
        by simp        
      hence \<open>(2^l) * post_H = 0\<close>
        by (simp add: \<open>post_H = 0\<close>)        
      thus ?thesis
        unfolding pnorm_def
        by auto
    qed
    ultimately have \<open>pnorm 2 (((2^l) *  (inverse  (of_nat (2^l))) 
                                  + (2^l) * pre_H) + ((2^l) * post_H)) = 1\<close>
      using pnorm_unit_ball[where p = 2 and x = "(2^l) *  (inverse  (of_nat (2^l))) + (2^l) * pre_H" 
          and y = "(2^l) * post_H"]
      by simp
    moreover have \<open>2 ^ l * inverse (rat_of_nat (2 ^ l)) + 2 ^ l * pre_H + 2 ^ l * post_H 
          = 2^l * Harm n\<close>
      using \<open>Harm n = pre_H + (inverse  (of_nat (2^l))) + post_H\<close>
      by (simp add: semiring_normalization_rules(34))      
    ultimately show ?thesis
      by auto      
  qed
  hence \<open>(pnorm 2 (2^l)) * (pnorm 2 (Harm n)) = 1\<close>
    using Pnorm.pnorm_mult \<open>prime 2\<close>
    by auto
  hence \<open>(1/2^l) * (pnorm 2 (Harm n)) = 1\<close>
  proof-
    have \<open>prime (2::nat)\<close>
      by simp
    hence \<open>pnorm 2 (2^l) = 1/2^l\<close>
      using pnorm_primepow[where p = 2 and l = "l"] 
      by simp
    thus ?thesis
      using \<open>pnorm 2 (2 ^ l) * pnorm 2 (Harm n) = 1\<close> 
      by auto
  qed
  hence \<open>pnorm 2 (Harm n) = 2^l\<close>
    by simp
  thus ?thesis
    by (simp add: l_def)
qed

lemma Harm_mono: "m \<noteq> 0 \<Longrightarrow> 2*m \<le> n \<Longrightarrow> pnorm 2 (Harm m) < pnorm 2 (Harm n)"
proof-
  assume \<open>m \<noteq> 0\<close> and \<open>2*m \<le> n\<close>
  have \<open>m \<ge> 1\<close>
    using \<open>m \<noteq> 0\<close> by linarith
  have \<open>pnorm 2 (Harm m) =  2 ^ nat \<lfloor>log 2 (real m)\<rfloor>\<close>
    using harmonic_numbers_2norm[where n = "m"] \<open>m \<noteq> 0\<close>    
    by auto
  moreover have \<open>pnorm 2 (Harm n) =  2 ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
    using harmonic_numbers_2norm[where n = "n"] \<open>2 * m \<le> n\<close> \<open>m \<noteq> 0\<close> by linarith 
  moreover have \<open>(2::nat) ^ nat \<lfloor>log 2 (real m)\<rfloor> < (2::nat) ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
  proof-
    have \<open>log 2 (real m) + 1 = log 2 (real m) + log 2 (2::real)\<close>
    proof-
      have \<open>log 2 (real 2) = 1\<close>
        by simp
      thus ?thesis 
        by simp
    qed
    also have \<open>\<dots> = log 2 ((real m) * (2::real)) \<close>
    proof-
      have \<open>(2::real) > 0\<close>
        by simp
      moreover have \<open>(2::real) \<noteq> 1\<close>
        by simp
      ultimately show ?thesis
        using \<open>m \<ge> 1\<close> log_mult[where a = 2 and x = "real m" and y = "2::real"]         
        by simp
    qed
    also have \<open>\<dots> = log 2 (2*real m) \<close>
    proof-
      have \<open>(real m)*(2::real) = 2*m\<close>
        by auto
      thus ?thesis
        by (simp add: \<open>real m * 2 = real (2 * m)\<close>)             
    qed
    also have \<open>\<dots> \<le> log 2 (real n)\<close>
      using \<open>2*m \<le> n\<close> \<open>m \<noteq> 0\<close> by auto
    finally have \<open>log 2 (real m) + 1 \<le> log 2 (real n)\<close>
      by blast
    hence \<open>\<lfloor>log 2 (real m)\<rfloor> < \<lfloor>log 2 (real n)\<rfloor>\<close>
      by linarith
    moreover have \<open>\<lfloor>log 2 (real m)\<rfloor> \<ge> 0\<close>
    proof-
      have \<open>log 2 (real m) \<ge> 0\<close>
        using \<open>m \<ge> 1\<close> by auto
      thus ?thesis by auto
    qed
    ultimately have \<open>nat \<lfloor>log 2 (real m)\<rfloor> < nat \<lfloor>log 2 (real n)\<rfloor>\<close>
      using nat_less_eq_zless by blast      
    moreover have \<open>(2::nat) > 1\<close>
      by auto
    ultimately show ?thesis
      using power_strict_increasing[where a = "2::nat" and n = "nat \<lfloor>log 2 (real m)\<rfloor>" 
          and N = "nat \<lfloor>log 2 (real n)\<rfloor>"] by blast
  qed
  ultimately show ?thesis 
    by auto
qed

subsection \<open>Main results\<close>

text\<open>The following result is due to L. Taeisinger ~\cite{theisinger1915bemerkung}.\<close>
theorem Taeisinger:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>Harm n \<notin> \<int>\<close>
proof-
  have  \<open>prime (2::nat)\<close>
    by simp
  moreover have \<open>pnorm 2 (Harm n) > 1\<close>    
    using harmonic_numbers_2norm[where n = "n"] \<open>n \<ge> 2\<close> 
    by auto
  ultimately show ?thesis
    using integers_pnorm[where x = "Harm n"] by smt
qed

text\<open>The following result is due to J. K{\"u}rsch{\'a}k  ~\cite{kurschak1918harmonic}.\<close>
theorem Kurschak:
  fixes n m :: nat
  assumes \<open>m + 2 \<le> n\<close>
  shows \<open>Harm n - Harm m \<notin> \<int>\<close>
proof(cases \<open>2*m \<le> n\<close>)
  case True show ?thesis
  proof(cases \<open>m = 0\<close>)
    case True thus ?thesis using Taeisinger assms by auto
  next
    case False
    have \<open>n \<ge> 2\<close>
      using \<open>m+2 \<le> n\<close> by auto
    have \<open>prime (2::nat)\<close>
      by auto
    have \<open>Harm n = (Harm n - Harm m) + (Harm m)\<close>
      by simp
    hence \<open>pnorm 2 (Harm n) \<le> max (pnorm 2 (Harm n - Harm m)) (pnorm 2 (Harm m))\<close>
      using pnorm_add_le[where p = "2::nat" and x = "Harm n - Harm m" and y = "Harm m"] by simp
    moreover have \<open>pnorm 2 (Harm m) < pnorm 2 (Harm n)\<close>
      by (simp add: False Harm_mono True)      
    ultimately have \<open>pnorm 2 (Harm n) \<le> pnorm 2 (Harm n - Harm m)\<close>
      by linarith
    moreover have \<open>1 < pnorm 2 (Harm n)\<close>
      using harmonic_numbers_2norm[where n = "n"] \<open>n \<ge> 2\<close> by auto
    ultimately have \<open>1 < pnorm 2 (Harm n - Harm m)\<close>
      by auto
    thus ?thesis
      using integers_pnorm[where x = "Harm n - Harm m"] \<open>prime 2\<close> by smt
  qed
next
  case False
  have \<open>n \<ge> m\<close>
    using add_leE assms by blast
  have \<open>Harm n - Harm m < 1\<close>
    using False Harm_diff_less_1 assms by auto    
  moreover have \<open>0 < Harm n - Harm m\<close>
    using Harm_incre \<open>m+2 \<le> n\<close> by simp
  have f1: "sgn (Harm n - Harm m) = 1"
    by (metis \<open>0 < Harm n - Harm m\<close> sgn_pos)
  have "0 \<le> Harm n - Harm m"
    by (metis \<open>0 < Harm n - Harm m\<close> less_eq_rat_def)
  thus ?thesis using f1 \<open>Harm n - Harm m < 1\<close> frac_eq_0_iff sgn_if zero_neq_one frac_eq by metis
qed

end

