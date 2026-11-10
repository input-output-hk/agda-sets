{ pkgs, pagda }:

{
  docs = pagda.docBackends.enhancedHtml {
    entryModule = "abstract-set-theory";
    githubUrl = "https://github.com/input-output-hk/agda-sets";
  };
}
