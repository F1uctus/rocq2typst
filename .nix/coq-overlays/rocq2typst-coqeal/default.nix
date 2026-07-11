{
  lib,
  mkCoqDerivation,
  coq,
  rocq2typst-mathcomp,
  coqeal,
  version ? ../../../.,
}:

mkCoqDerivation {
  pname = "rocq2typst-coqeal";
  opam-name = "rocq2typst-coqeal";
  inherit version;
  useDune = true;

  propagatedBuildInputs = [ rocq2typst-mathcomp coqeal ];

  meta = {
    description = "CoqEAL notation dictionary for rocq2typst";
    license = lib.licenses.gpl3Plus;
  };
}
