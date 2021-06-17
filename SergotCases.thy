theory SergotCases

imports Main Sergot SergotTheorems

begin

consts a :: "\<mu>" 
consts b :: "\<mu>"
consts c :: "\<mu>"
consts d :: "\<mu>"
consts k :: "\<sigma>"
consts apushes:: "i set"
consts bpushes:: "i set"
consts cpushes:: "i set"
consts dpushes:: "i set"

locale Overdetermination =
assumes "Ag = {a, b}"
and "apushes \<in> (\<^bold>A\<^sub> a)"
and "bpushes \<in> (\<^bold>A\<^sub> b)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<notin> bpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<in> bpushes)" 
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes)" 
and "a \<noteq> b"
and a: "\<forall>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>.(\<tau> \<in> apushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>.(\<tau> \<in> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>k)"


locale Pairs =
assumes "Ag = {a, b, c}"
and "apushes \<in> (\<^bold>A\<^sub> a)"
and "bpushes \<in> (\<^bold>A\<^sub> b)"
and "bpushes \<in> (\<^bold>A\<^sub> c)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes \<and> \<tau> \<in> cpushes)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<notin> bpushes \<and> \<tau> \<in> cpushes)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes \<and> \<tau> \<notin> cpushes)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<notin> bpushes \<and> \<tau> \<notin> cpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<in> bpushes \<and> \<tau> \<in> cpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes \<and> \<tau> \<in> cpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<in> bpushes \<and> \<tau> \<notin> cpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes \<and> \<tau> \<notin> cpushes)"
and "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
and "\<forall>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> cpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>. (\<tau> \<in> bpushes \<and> \<tau> \<in> cpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> k)"
and "\<forall>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> cpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> k)"
and "\<forall>\<tau>. (\<tau> \<notin> bpushes \<and> \<tau> \<notin> cpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> k)"


locale Underdetermination =
assumes "Ag = {a, b}"
and ap: "apushes \<in> (\<^bold>A\<^sub> a)"
and bp: "bpushes \<in> (\<^bold>A\<^sub> b)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes)"
and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<notin> bpushes)"
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<in> bpushes)" 
and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes)" 
and "a \<noteq> b"
and a: "\<forall>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>.(\<tau> \<notin> apushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile>(\<^bold>\<not>k)"
and "\<forall>\<tau>.(\<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile>(\<^bold>\<not>k)"
and "\<forall>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>k)"


consts s :: "\<mu>"
consts j :: "\<mu>"
consts jjumps :: "i set" 
consts sshoots :: "i set" 

locale JumpersNonDet =
assumes "Ag = {s, j}"
and ap: "jjumps \<in> (\<^bold>A\<^sub> j)"
and bp: "sshoots \<in> (\<^bold>A\<^sub> s)"
and "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots)"
and "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<notin> sshoots)"
and "\<not> (\<exists>\<tau>. (\<tau> \<notin> jjumps \<and> \<tau> \<in> sshoots))" 
and e: "\<exists>\<tau>. (\<tau> \<notin> jjumps \<and> \<tau> \<notin> sshoots)" 
and "s \<noteq> j"
and a: "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots \<and> \<tau> \<^bold>\<Turnstile> k)"
and b: "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>k))"
and c: "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<notin> sshoots \<and> \<tau> \<^bold>\<Turnstile> k)"
and d: "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<notin> sshoots \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>k))"
and f: "\<forall>\<tau>.(\<tau> \<notin> jjumps) \<longrightarrow> \<tau> \<^bold>\<Turnstile>(\<^bold>\<not>k)"

locale JumpersDet =
assumes "Ag = {s, j}"
and ap: "jjumps \<in> (\<^bold>A\<^sub> j)"
and bp: "sshoots \<in> (\<^bold>A\<^sub> s)"
and "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<in> sshoots)"
and "\<exists>\<tau>. (\<tau> \<in> jjumps \<and> \<tau> \<notin> sshoots)"
and "\<not> (\<exists>\<tau>. (\<tau> \<notin> jjumps \<and> \<tau> \<in> sshoots))" 
and "\<exists>\<tau>. (\<tau> \<notin> jjumps \<and> \<tau> \<notin> sshoots)" 
and "s \<noteq> j"
and a: "\<forall>\<tau>. (\<tau> \<in> jjumps \<longrightarrow> \<tau> \<^bold>\<Turnstile> k)"
and b: "\<forall>\<tau>. (\<tau> \<in> sshoots \<longrightarrow> \<tau> \<^bold>\<Turnstile> k)"
and "\<forall>\<tau>.(\<tau> \<notin> jjumps) \<longrightarrow> \<tau> \<^bold>\<Turnstile>(\<^bold>\<not>k)"


consts athrows::"i set"
consts bthrows::"i set"
consts g::"\<sigma>"

locale Throwers =
assumes "Ag = {a, b}"
and "a \<noteq> b"
and at: "athrows \<in> (\<^bold>A\<^sub> a)"
and bt: "bthrows \<in> (\<^bold>A\<^sub> b)"
and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<in> bthrows)"
and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<notin> bthrows)"
and "\<not> (\<exists>\<tau>. (\<tau> \<notin> athrows \<and> \<tau> \<in> bthrows))" 
and "\<exists>\<tau>. (\<tau> \<notin> athrows \<and> \<tau> \<notin> bthrows)" 
and a: "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<^bold>\<Turnstile> g)"
and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<notin> bthrows \<and>\<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g))"
and b: "\<forall>\<tau>. (\<tau> \<in> bthrows \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g))"
and "\<forall>\<tau>.(\<tau> \<notin> athrows \<and> \<tau> \<notin> bthrows) \<longrightarrow> \<tau> \<^bold>\<Turnstile> g"


consts abringsvase::"i set" \<comment> \<open>the action of a bringing the vase outside\<close>
consts bbringsvase::"i set" \<comment> \<open>the action of b bringing the vase outside\<close>
consts inside::"\<sigma>" \<comment> \<open>the vase is inside\<close>
consts rain::"\<sigma>" \<comment> \<open>it is raining\<close>
consts wet::"\<sigma>" \<comment> \<open>the vase is wet\<close>

locale Vase =
assumes "Ag = {a, b}" \<comment> \<open>We only have two agents\<close>
and "a \<noteq> b" \<comment> \<open>they are different\<close>
and"wet = \<^bold>\<not>inside \<^bold>\<and> rain" \<comment> \<open>the vase is ruined if it's outside and it rains\<close>
and at: "abringsvase \<in> (\<^bold>A\<^sub> a)" \<comment> \<open>abringsvase is an action of agent a\<close>
and bt: "bbringsvase \<in> (\<^bold>A\<^sub> b)" \<comment> \<open>bbringsvase is an action of agent b\<close>
and "(UNIV::i set) - abringsvase \<in> (\<^bold>A\<^sub> a)" \<comment> \<open>so is not bringing the vase\<close>
and "(UNIV::i set) - bbringsvase \<in> (\<^bold>A\<^sub> b)"
and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<notin> bbringsvase)" \<comment> \<open>It is possible for a to bring the vase but not b\<close>
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<in> bbringsvase)" \<comment> \<open>and vice verse\<close>
and "\<not> (\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<in> bbringsvase))" \<comment> \<open>Both cannot bring the vase outside (optional)\<close>
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<notin> bbringsvase)" \<comment> \<open>No one must bring it outside\<close>
and "\<forall>\<tau>. (\<tau> \<in> abringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>inside))" \<comment> \<open>if brought outside (by a) the vase is outside\<close>
and "\<forall>\<tau>. (\<tau> \<in> bbringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> inside))" \<comment> \<open>if brought outside (by b) the vase is outside\<close>
and "\<forall>\<tau>. (\<tau> \<notin> abringsvase \<longrightarrow> \<tau> \<notin> bbringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> inside)" \<comment> \<open>By default the vase is inside\<close>
and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<^bold>\<Turnstile> rain)"  \<comment> \<open>It might rain\<close>
and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))" \<comment> \<open>Or not\<close>
and "\<exists>\<tau>. (\<tau> \<in> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> rain)"  \<comment> \<open>same if b takes the vase\<close>
and "\<exists>\<tau>. (\<tau> \<in> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))"
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<notin> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> rain)"  \<comment> \<open>or no one brings it\<close>
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<notin> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))"

end