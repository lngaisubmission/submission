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

locale Overdetermination  =
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


locale Underdetermination  =
  assumes "Ag = {a, b}"
    and ap: "apushes \<in> (\<^bold>A\<^sub> a)"
    and bp: "bpushes \<in> (\<^bold>A\<^sub> b)"
    and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes)"
    and "\<exists>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<notin> bpushes)"
    and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<in> bpushes)" 
    and "\<exists>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes)" 
    and "a \<noteq> b"
and a: "\<forall>\<tau>. (\<tau> \<in> apushes \<and> \<tau> \<in> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> k"
and "\<forall>\<tau>.(\<tau> \<notin> apushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile>  (\<^bold>\<not>k)"
and "\<forall>\<tau>.(\<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile>  (\<^bold>\<not>k)"
and "\<forall>\<tau>. (\<tau> \<notin> apushes \<and> \<tau> \<notin> bpushes) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not>k)"

consts s :: "\<mu>"
consts j :: "\<mu>"
consts jjumps :: "i set" 
consts sshoots :: "i set" 
consts k::"\<sigma>"
locale JumpersNonDet  =
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
and f: "\<forall>\<tau>.(\<tau> \<notin> jjumps) \<longrightarrow> \<tau> \<^bold>\<Turnstile>  (\<^bold>\<not>k)"

locale JumpersDet  =
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
and "\<forall>\<tau>.(\<tau> \<notin> jjumps) \<longrightarrow> \<tau> \<^bold>\<Turnstile>  (\<^bold>\<not>k)"

consts athrows::"i set"
consts bthrows::"i set"
consts g::"\<sigma>"
locale Throwers  =
  assumes "Ag = {a, b}"
    and "a \<noteq> b"
    and at: "athrows \<in> (\<^bold>A\<^sub> a)"
    and bt: "bthrows \<in> (\<^bold>A\<^sub> b)"
    and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<in> bthrows)"
    and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<notin> bthrows)"
    and "\<not> (\<exists>\<tau>. (\<tau> \<notin> athrows \<and> \<tau> \<in> bthrows))" 
    and "\<exists>\<tau>. (\<tau> \<notin> athrows \<and> \<tau> \<notin> bthrows)" 
and a: "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<^bold>\<Turnstile> g)"
and "\<exists>\<tau>. (\<tau> \<in> athrows \<and> \<tau> \<notin> bthrows \<and>  \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g))"
and b: "\<forall>\<tau>. (\<tau> \<in> bthrows \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> g))"
and "\<forall>\<tau>.(\<tau> \<notin> athrows \<and> \<tau> \<notin> bthrows) \<longrightarrow> \<tau> \<^bold>\<Turnstile> g"


consts abringsvase::"i set"
consts bbringsvase::"i set"
consts inside::"\<sigma>"
consts rain::"\<sigma>"
consts wet::"\<sigma>"
locale Vase  =
assumes "Ag = {a, b}"
    and "a \<noteq> b"
    and  "wet = (\<^bold>\<not> inside) \<^bold>\<and> rain"
    and at: "abringsvase \<in> (\<^bold>A\<^sub> a)"
    and bt: "bbringsvase \<in> (\<^bold>A\<^sub> b)"
    and "(UNIV::i set) - abringsvase \<in> (\<^bold>A\<^sub> a)"
    and "(UNIV::i set) - bbringsvase \<in> (\<^bold>A\<^sub> b)"
    and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<notin> bbringsvase)"
    and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<in> bbringsvase)"
    and "\<not> (\<exists>\<tau>. (\<tau> \<in> abringsvase \<and> \<tau> \<in> bbringsvase))" 
    and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and> \<tau> \<notin> bbringsvase)" 
and "\<forall>\<tau>. (\<tau> \<in> abringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> inside))"
and "\<forall>\<tau>. (\<tau> \<in> bbringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> inside))"
and "\<forall>\<tau>. (\<tau> \<notin> abringsvase \<longrightarrow> \<tau> \<notin> bbringsvase \<longrightarrow> \<tau> \<^bold>\<Turnstile> inside)"

and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and>  \<tau> \<^bold>\<Turnstile> rain)"
and "\<exists>\<tau>. (\<tau> \<in> abringsvase \<and>  \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))"
and "\<exists>\<tau>. (\<tau> \<in> bbringsvase \<and>  \<tau> \<^bold>\<Turnstile> rain)"
and "\<exists>\<tau>. (\<tau> \<in> bbringsvase \<and>  \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))"
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and>  \<tau> \<notin> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> rain)"
and "\<exists>\<tau>. (\<tau> \<notin> abringsvase \<and>  \<tau> \<notin> bbringsvase \<and> \<tau> \<^bold>\<Turnstile> (\<^bold>\<not> rain))"



end