{ pkgs ? import (builtins.fetchTarball
  https://github.com/nixos/nixpkgs/tarball/7438ebd9431243aa0b01502fae89c022e4facb0c) {} }:

with pkgs;
let
  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE = if pkgs.system == "x86_64-linux"
                     then "${pkgs.glibcLocales}/lib/locale/locale-archive"
                     else "";
  };

  agdaStdlib = agdaPackages.standard-library;

  agdaStdlibClasses = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-classes";
    version = "2.0";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "omelkonian";
      rev = "5d77a54d6cd31da8a65b9cfca691f214d1c05184";
      sha256 = "sha256-WEQ6UmHFCDq/PyArJ7u0SQ6q+JYzoMHoMG0psGYzZ8A=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.1.1";
    src = fetchFromGitHub {
      repo = "stdlib-meta";
      owner = "omelkonian";
      rev = "v2.1.1";
      sha256 = "qOoThYMG0dzjKvwmzzVZmGcerfb++MApbaGRzLEq3/4=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "Main.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  agdaWithPkgs = p: agda.withPackages { pkgs = p; };

in
{
  agda-abstract-set-theory = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-abstract-set-theory";
    version = "0.1";
    meta = { };
    src = ./.;
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = deps;
    # postInstall = ''
    #   sh checkTypeChecked.sh
    # '';
  };
}
