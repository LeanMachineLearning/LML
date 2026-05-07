import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre.Manual
open Verso.Genre.Manual.Bibliography

@[bib "lattimore2020bandit"]
def lattimore2020bandit : Verso.Genre.Manual.Bibliography.Citable := .article {
  title := inlines!"Bandit algorithms"
  authors := #[inlines!"Tor Lattimore", inlines!"Csaba Szepesvári"]
  year := 2020
  journal := inlines!"Cambridge University Press"
  month := none
  volume := inlines!"0"
  number := inlines!"0"
}

@[bib "marion2025formalization"]
def marion2025formalization : Verso.Genre.Manual.Bibliography.Citable := .arXiv {
  title := inlines!"A Formalization of the Ionescu-Tulcea Theorem in Mathlib"
  authors := #[inlines!"Etienne Marion"]
  year := 2025
  id := "2506.18616"
}
