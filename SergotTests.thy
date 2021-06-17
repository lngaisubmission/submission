theory SergotTests

imports Main SergotCoulds SergotCases

begin
nitpick_params[user_axioms, timeout = 300]

section "(In)Dependence of Coulds"

lemma 12: "\<lfloor>(Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*) 
lemma 13: "\<lfloor>(Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)
lemma 14: "\<lfloor>(Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)

lemma 21: "\<lfloor>(Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)
lemma 23: "\<lfloor>(Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)
lemma 24: "\<lfloor>(Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)

lemma 31: "\<lfloor>(Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*) 
lemma 32: "\<lfloor>(Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)
lemma 34: "\<lfloor>(Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)

lemma 41: "\<lfloor>(Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops(*nitpick finds a counterexample*) 
lemma 42: "\<lfloor>(Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)
lemma 43: "\<lfloor>(Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<^bold>\<rightarrow> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)\<rfloor>" oops (*nitpick finds a counterexample*)

  
section "Cases"

lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {a,b} g)))" 
  (*by (metis Diff_cancel Throwers_axioms Throwers_def UNIV_I equals0D mem_Collect_eq tildeeqU tildexeq)*) oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {a,b} g)))"
  (*by (smt (verit) Throwers_axioms Throwers_def UNIV_I mem_Collect_eq tildexeq) *) oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {a,b} g)))" 
  using a by blast
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {a,b} g)))" 
  (*by (smt (verit) Throwers_axioms Throwers_def UNIV_I mem_Collect_eq tildexeq) *) oops

lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {a} g)))" oops
lemma (in Throwers) "\<not> (\<forall>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {a} g)))" 
  by (smt (verit, del_insts) Diff_insert_absorb Throwers_axioms Throwers_def insertCI mem_Collect_eq singletonD tildeeqU tildexeq) 
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {b} g)))"  oops
lemma (in Throwers) " \<not> (\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {b} g)))" oops

lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))"
  (* by (metis Throwers_axioms Throwers_def insert_subset mem_Collect_eq psubsetI singletonD subsetI tildexeq)*) oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" 
  by (metis Throwers_axioms Throwers_def bot.not_eq_extremum insert_not_empty) 
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a,b} g)))" oops


lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops
lemma (in Throwers) "((\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))"  oops
lemma (in Throwers) "\<not>(\<forall>\<tau>.(\<tau> \<in> athrows \<and> \<tau> \<in> bthrows) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} g)))" oops



lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet))))" oops
lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {a} (\<^bold>\<not> wet)))"  oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {a} (\<^bold>\<not> wet))))" oops

lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet))))" 
  (*by (metis Vase_axioms Vase_def mem_Collect_eq singletonD tildeeqU tildexeq)*) oops
lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {a} (\<^bold>\<not> wet))))" oops

lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet))))"oops 
(*  by (metis Vase_axioms Vase_def bot.not_eq_extremum insert_not_empty) *)
lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {a} (\<^bold>\<not> wet)))" 
  by (meson singletonI tildexeq)
lemma (in Vase) "\<not> ((\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {a} (\<^bold>\<not> wet))))" oops

lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} (\<^bold>\<not> wet))))" oops
lemma (in Vase) "(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {a} (\<^bold>\<not> wet)))" oops
lemma (in Vase) " \<not> (\<forall>\<tau>.(\<tau> \<in> abringsvase) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> wet) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {a} (\<^bold>\<not> wet))))" oops


lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample*)oops
lemma (in JumpersDet) " \<not> (\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample? ? *) oops
lemma (in JumpersDet) " \<not> (\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {j} \<^bold>\<not> k)))" oops

lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" 
  (*by (smt (verit, del_insts) Diff_insert_absorb JumpersDet_axioms JumpersDet_def ac empty_subsetI insert_subset leD less_le mem_Collect_eq singleton_iff singleton_insert_inj_eq' tildeeqU) *) oops
lemma (in JumpersDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample*) oops
lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {j} \<^bold>\<not> k)))" 
  by (smt (z3) JumpersDet_axioms JumpersDet_def ac insertI1 mem_Collect_eq) 
lemma (in JumpersDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample*) oops

lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample ? ? *) oops
lemma (in JumpersDet) "\<not>(\<forall>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" 
  by (metis JumpersDet_axioms JumpersDet_def bot.not_eq_extremum insert_not_empty) 
lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {j} \<^bold>\<not> k)))" 
  by (meson singletonI tildexeq)
lemma (in JumpersDet) "\<not>(\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {j} \<^bold>\<not> k)))" (*nitpick finds a counterexample*) oops

lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))"
 (* by (metis JumpersDet_axioms JumpersDet_def empty_subsetI insertCI insert_subset leD less_le mem_Collect_eq singletonD tildeeqU tildexeq) *) oops
lemma (in JumpersDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))"(*nitpick finds a counterexample*) oops
lemma (in JumpersDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {j} \<^bold>\<not> k)))" 
  (*by (metis JumpersDet_axioms JumpersDet_def mem_Collect_eq singletonacc tildexeq) *) oops
lemma (in JumpersDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {j} \<^bold>\<not> k)))" (*Nitpick finds a counterexample*) oops


lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could\<^sub> {j} \<^bold>\<not> k)))" 
 (*by (metis DiffI JumpersNonDet_axioms JumpersNonDet_def UNIV_I mem_Collect_eq singletonD tildeeqU tildexeq) *)oops

lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))"
 (* by (smt (verit, ccfv_threshold) Diff_insert_absorb ac ap emptyE empty_subsetI f insertI1 insert_subset mem_Collect_eq psubsetE singleton_insert_inj_eq' tildeeqU) *) oops
lemma (in JumpersNonDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {j} \<^bold>\<not> k)))" 
  by (meson ac ap f insertI1)
lemma (in JumpersNonDet) "\<not>((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could2\<^sub> {j} \<^bold>\<not> k)))" oops

lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))"
  by (meson a b bot.not_eq_extremum insert_not_empty)
lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {j} \<^bold>\<not> k)))"
  using d by blast
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could3\<^sub> {j} \<^bold>\<not> k)))"oops

lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" 
  (*by (metis Diff_insert_absorb ap e empty_iff empty_subsetI f insertI1 insert_subset mem_Collect_eq psubsetE singleton_insert_inj_eq tildeeqU tildexeq) *)oops
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> {j} \<^bold>\<not> k)))" oops
lemma (in JumpersNonDet) "((\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {j} \<^bold>\<not> k)))" 
 (* by (smt (verit, del_insts) JumpersNonDet.e JumpersNonDet_axioms ap f mem_Collect_eq singletonI tildexeq) *)oops
lemma (in JumpersNonDet) "\<not>(\<forall>\<tau>.(\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> k) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Could4\<^sub> {j} \<^bold>\<not> k)))" oops


end