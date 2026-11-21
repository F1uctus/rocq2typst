{
  lib,
  mkCoqDerivation,
  coq,
  rocq2typst,
  mathcomp-algebra,
  mathcomp-fingroup,
  version ? ../../../.,
}:

mkCoqDerivation {
  pname = "rocq2typst-mathcomp";
  opam-name = "rocq2typst-mathcomp";
  inherit version;
  useDune = true;

  propagatedBuildInputs = [ rocq2typst mathcomp-algebra mathcomp-fingroup ];

  meta = {
    description = "Mathematical Components notation dictionary for rocq2typst";
    license = lib.licenses.gpl3Plus;
  };
}
