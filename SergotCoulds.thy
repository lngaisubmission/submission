theory SergotCoulds

imports Sergot

begin

abbreviation tildeGconv :: "i\<Rightarrow> (\<mu> set)\<Rightarrow>i\<Rightarrow>bool" ("_ -~-_ _")
 where "(\<tau>a -~- (G::\<mu> set) \<tau>b) \<equiv> (\<tau>a \<^bold>~ \<tau>b) \<and> (\<forall>x. ((x \<in> G) \<longrightarrow> \<not>(\<tau>a::i)\<^bold>~x(\<tau>b::i)))" 
(* check if better encoding possible*)

abbreviation mstitconv :: "\<mu> set \<Rightarrow> \<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<lbrakk> _ \<^bold>\<rbrakk> _"[52]53)
 where "\<^bold>\<lbrakk>(G::\<mu> set)\<^bold>\<rbrakk> \<phi> \<equiv> \<lambda>(w::i).\<forall>(v::i). (w -~- G v) \<longrightarrow> \<phi>(v)"
abbreviation mstitconvDia :: "\<mu> set \<Rightarrow> \<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<llangle> _ \<^bold>\<rrangle> _"[52]53)
 where "\<^bold>\<llangle>(G::\<mu> set)\<^bold>\<rrangle> \<phi> \<equiv> \<lambda>(w::i).\<exists>(v::i). (w -~- G v) \<longrightarrow> \<phi>(v)"

abbreviation Could2 :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could2\<^sub> _ _")
 where "Could2\<^sub> G \<phi> \<equiv> \<^bold>\<lbrakk>(G::\<mu> set)\<^bold>\<rbrakk> (\<phi>)"

abbreviation Could2min :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> _ _")
 where "(Could2\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) (\<tau>::i) \<equiv> ((Could2\<^sub> G \<phi>) \<tau>) \<and> \<not>(\<exists> H. (H \<subset> G) \<and> ((Could2\<^sub> H \<phi>) \<tau>))"

abbreviation Could3 :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could3\<^sub> _ _")
 where "Could3\<^sub> G \<phi> \<equiv> \<^bold>\<llangle>(G::\<mu> set)\<^bold>\<rrangle> \<phi>"

abbreviation Could3min :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> _ _")
 where "(Could3\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) (\<tau>::i) \<equiv> ((Could3\<^sub> G \<phi>) \<tau>) \<and> \<not>(\<exists> H. (H \<subset> G) \<and> ((Could3\<^sub> H \<phi>) \<tau>))"

abbreviation Could4 :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could4\<^sub> _ _")
 where "Could4\<^sub> G \<phi> \<equiv> \<^bold>\<diamond> \<^bold>[G\<^bold>]\<phi>"

abbreviation Could4min :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> _ _")
 where "(Could4\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) (\<tau>::i) \<equiv> ((Could4\<^sub> G \<phi>) \<tau>) \<and> \<not>(\<exists> H. (H \<subset> G) \<and> ((Could4\<^sub> H \<phi>) \<tau>))"


end