{
  lib,
  mkCoqDerivation,
  coq,
  rocq2typst,
  mathcomp-infotheo,
  version ? ../../../.,
}:

mkCoqDerivation {
  pname = "rocq2typst-infotheo";
  opam-name = "rocq2typst-infotheo";
  inherit version;
  useDune = true;

  propagatedBuildInputs = [ rocq2typst mathcomp-infotheo ];

  meta = {
    description = "Infotheo notation dictionary for rocq2typst";
    license = lib.licenses.gpl3Plus;
  };
}
