{
  lib,
  mkCoqDerivation,
  coq,
  rocq2typst-mathcomp,
  mathcomp-analysis,
  micromega-plugin,
  version ? ../../../.,
}:

mkCoqDerivation {
  pname = "rocq2typst-analysis";
  opam-name = "rocq2typst-analysis";
  inherit version;
  useDune = true;

  propagatedBuildInputs = [ rocq2typst-mathcomp mathcomp-analysis micromega-plugin ];

  meta = {
    description = "Mathcomp-analysis notation dictionary for rocq2typst";
    license = lib.licenses.gpl3Plus;
  };
}
