#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Cipher Machine & Cryptanalysis Suite  (cipher_suite.py)
=======================================================

A self-contained toolkit (standard library only, Python 3.10+) for studying
classical ciphers and the statistical attacks that break them.

    Ciphers          Caesar, ROT-N, Affine, Vigenere (+Autokey), Playfair,
                     columnar transposition, XOR (repeating key / hash stream),
                     Enigma-style rotor machine (3 rotors, reflector, plugboard)
    Cryptanalysis    brute force, chi-squared + index-of-coincidence ranking,
                     Kasiski / IoC key-length estimation, automatic Vigenere
                     and repeating-key XOR breakers, text analyser
    Alphabets        English, Arabic (with optional letter folding) and any
                     custom alphabet; case and non-letters are preserved
    Interfaces       interactive menu, direct sub-commands, JSON batch jobs,
                     file input/output, built-in unittest suite

EDUCATIONAL USE ONLY: every cipher here is historical or a teaching toy.
None of them protects real data.

Quick start
-----------
    python cipher_suite.py                       # interactive menu
    python cipher_suite.py demo                  # guided tour
    python cipher_suite.py list                  # ciphers and parameters
    python cipher_suite.py encrypt caesar --shift 3 --text "Hello, World!"
    python cipher_suite.py decrypt vigenere --key LEMON --file cipher.txt -o plain.txt
    python cipher_suite.py encrypt vigenere --key QUEENLY --mode autokey --text "ATTACK AT DAWN"
    python cipher_suite.py encrypt caesar --alphabet arabic --shift 5 --text "مرحبا بالعالم"
    python cipher_suite.py crack caesar --file secret.txt --top 3
    python cipher_suite.py crack vigenere --file secret.txt --max-key-length 16
    python cipher_suite.py keylen --file secret.txt
    python cipher_suite.py analyze --file secret.txt
    python cipher_suite.py batch jobs.json -o results.json
    python cipher_suite.py test                  # or: python -m unittest cipher_suite

Windows PowerShell tips for Arabic / Unicode text
-------------------------------------------------
The program reconfigures stdin/stdout/stderr to UTF-8 on start-up and, on
Windows, switches the console code page to 65001.  If glyphs still look
broken, use a font with Arabic support (e.g. "Cascadia Mono" in Windows
Terminal) or pass text through files (--file / -o), which are always UTF-8.

Layout of this file (each section maps 1:1 to a module if you want to split it
into a package: alphabet.py, params.py, ciphers/, cryptanalysis.py, io.py, ...)

    1. Exceptions                      7. Cryptanalysis
    2. Alphabets                       8. Text & file I/O
    3. Number theory & parameters      9. Batch processing & facade
    4. Cipher base class & registry   10. Presentation helpers
    5. Classical ciphers              11. CLI + interactive menu
    6. Enigma rotor machine           12. Sample corpora, demo, unit tests
"""

from __future__ import annotations

import abc
import argparse
import base64
import binascii
import codecs
import contextlib
import hashlib
import io
import json
import math
import os
import re
import sys
import tempfile
import unicodedata
import unittest
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Callable, ClassVar, Iterable, Mapping, Sequence

__version__ = "1.0.0"


# ============================================================================
# SECTION 1 - EXCEPTIONS
# ============================================================================

class CipherSuiteError(Exception):
    """Base class for every error raised deliberately by this suite."""


class AlphabetError(CipherSuiteError):
    """An alphabet definition or alphabet selection is invalid."""


class InvalidKeyError(CipherSuiteError):
    """A key or cipher parameter is missing, malformed or mathematically invalid."""


class InvalidInputError(CipherSuiteError):
    """The text to process is empty, malformed or otherwise unusable."""


class EncodingFormatError(CipherSuiteError):
    """Hex / Base64 / UTF-8 conversion of cipher data failed."""


class UnknownCipherError(CipherSuiteError):
    """The requested cipher or attack method does not exist."""


class AnalysisError(CipherSuiteError):
    """A cryptanalysis routine cannot run (too little text, no letters, ...)."""


class BatchError(CipherSuiteError):
    """A batch job file or job description is malformed."""


class FileAccessError(CipherSuiteError):
    """A file could not be read or written."""


# ============================================================================
# SECTION 2 - ALPHABETS
# ============================================================================

class Alphabet:
    """An ordered set of letters used by substitution-style ciphers.

    * ``letters`` holds the canonical letters (upper case for cased scripts).
    * ``locate`` maps a character to ``(index, is_lower)`` or ``None`` so that
      ciphers can preserve case and pass every other character through.
    * ``fold`` is an optional lossy normalisation applied while reading text
      (e.g. Arabic alef variants -> bare alef).
    """

    __slots__ = ("name", "letters", "size", "fold", "_index", "_lower_index")

    def __init__(self, letters: str, name: str = "custom",
                 fold: Mapping[str, str] | None = None) -> None:
        if not isinstance(letters, str) or len(letters) < 2:
            raise AlphabetError("An alphabet needs at least two letters.")
        if len(set(letters)) != len(letters):
            dupes = "".join(sorted({c for c in letters if letters.count(c) > 1}))
            raise AlphabetError(f"Alphabet contains duplicate letters: {dupes!r}")
        self.name = name
        self.letters = letters
        self.size = len(letters)
        self._index = {c: i for i, c in enumerate(letters)}
        self._lower_index: dict[str, int] = {}
        for i, c in enumerate(letters):
            lower = c.lower()
            if lower != c and len(lower) == 1 and lower not in self._index:
                self._lower_index[lower] = i
        self.fold: dict[str, str] = {}
        for src, dst in (fold or {}).items():
            if dst not in self._index:
                raise AlphabetError(f"Fold target {dst!r} is not part of the alphabet.")
            self.fold[src] = dst

    @classmethod
    def custom(cls, letters: str, *, case_sensitive: bool = False,
               name: str = "custom") -> "Alphabet":
        """Build an alphabet from user text; letters are upper-cased unless
        ``case_sensitive`` so that lower-case input is still recognised."""
        letters = unicodedata.normalize("NFC", letters)
        if not case_sensitive:
            canonical = []
            for ch in letters:
                upper = ch.upper()
                canonical.append(upper if len(upper) == 1 else ch)
            letters = "".join(canonical)
        return cls(letters, name=name)

    def without_fold(self) -> "Alphabet":
        """Return a copy that does not normalise letter variants."""
        return Alphabet(self.letters, name=self.name)

    def locate(self, ch: str) -> tuple[int, bool] | None:
        """Return ``(index, is_lower)`` for a letter of this alphabet, else ``None``."""
        idx = self._index.get(ch)
        if idx is not None:
            return idx, False
        idx = self._lower_index.get(ch)
        if idx is not None:
            return idx, True
        target = self.fold.get(ch)
        if target is not None:
            return self._index[target], False
        return None

    def render(self, index: int, lower: bool = False) -> str:
        """Return the letter at ``index`` (mod size), optionally lower-cased."""
        letter = self.letters[index % self.size]
        return letter.lower() if lower else letter

    def transform(self, text: str, fn: Callable[[int], int]) -> str:
        """Apply ``fn`` to the index of every letter; keep all other characters."""
        out: list[str] = []
        for ch in text:
            loc = self.locate(ch)
            if loc is None:
                out.append(ch)
            else:
                out.append(self.render(fn(loc[0]), loc[1]))
        return "".join(out)

    def indices(self, text: str) -> list[int]:
        """Indices of the letters in ``text`` (everything else is ignored)."""
        result = []
        for ch in text:
            loc = self.locate(ch)
            if loc is not None:
                result.append(loc[0])
        return result

    def letters_only(self, text: str) -> str:
        """Canonical letters of ``text`` with all other characters removed."""
        return "".join(self.letters[i] for i in self.indices(text))

    def __repr__(self) -> str:
        return f"Alphabet(name={self.name!r}, size={self.size})"

    def __eq__(self, other: object) -> bool:
        return (isinstance(other, Alphabet) and self.letters == other.letters
                and self.fold == other.fold)

    def __hash__(self) -> int:
        return hash((self.letters, tuple(sorted(self.fold.items()))))


ENGLISH = Alphabet("ABCDEFGHIJKLMNOPQRSTUVWXYZ", name="english")

# 28 base letters; hamza and diacritics pass through untouched.  The fold map
# is a *lossy* normalisation: alef variants -> alef, ta marbuta -> ha,
# alef maksura -> ya.  Disable it with Alphabet.without_fold() / --no-fold.
ARABIC = Alphabet(
    "ابتثجحخدذرزسشصضطظعغفقكلمنهوي",
    name="arabic",
    fold={"أ": "ا", "إ": "ا", "آ": "ا", "ٱ": "ا", "ة": "ه", "ى": "ي"},
)


def get_alphabet(spec: str | None = None, *, fold: bool = True) -> Alphabet:
    """Resolve ``english`` | ``arabic`` | ``custom:<letters>`` into an Alphabet."""
    if spec is None or not str(spec).strip():
        return ENGLISH
    text = str(spec).strip()
    lowered = text.lower()
    if lowered in ("english", "en", "latin"):
        return ENGLISH
    if lowered in ("arabic", "ar"):
        return ARABIC if fold else ARABIC.without_fold()
    if lowered.startswith("custom:"):
        return Alphabet.custom(text[len("custom:"):])
    raise AlphabetError(
        f"Unknown alphabet {spec!r}. Use 'english', 'arabic' or 'custom:<letters>'.")


# ============================================================================
# SECTION 3 - NUMBER THEORY & PARAMETER HANDLING
# ============================================================================

def egcd(a: int, b: int) -> tuple[int, int, int]:
    """Extended Euclid: return ``(g, x, y)`` with ``a*x + b*y == g == gcd(a, b)``."""
    old_r, r = a, b
    old_x, x = 1, 0
    old_y, y = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_x, x = x, old_x - q * x
        old_y, y = y, old_y - q * y
    return old_r, old_x, old_y


def mod_inverse(a: int, m: int) -> int:
    """Modular multiplicative inverse of ``a`` mod ``m``; raises if none exists."""
    g, x, _ = egcd(a % m, m)
    if g != 1:
        raise InvalidKeyError(f"{a} has no inverse modulo {m} because gcd({a}, {m}) = {g}.")
    return x % m


def coprime_values(m: int) -> list[int]:
    """All ``a`` in ``1..m-1`` with ``gcd(a, m) == 1``."""
    return [a for a in range(1, m) if math.gcd(a, m) == 1]


def parse_int(value: Any, name: str = "value") -> int:
    """Strictly convert user input to ``int`` with a readable error message."""
    if isinstance(value, bool):
        raise InvalidKeyError(f"'{name}' must be an integer, not a boolean.")
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        if value.is_integer():
            return int(value)
        raise InvalidKeyError(f"'{name}' must be a whole number (got {value}).")
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            raise InvalidKeyError(f"'{name}' is empty; an integer is required.")
        try:
            return int(stripped, 10)
        except ValueError:
            raise InvalidKeyError(f"'{name}' must be an integer (got {value!r}).") from None
    raise InvalidKeyError(f"'{name}' must be an integer (got {type(value).__name__}).")


@dataclass(frozen=True)
class ParamSpec:
    """Declarative description of one cipher parameter (CLI flags, menu prompts, docs)."""
    name: str
    help: str
    default: Any = None
    required: bool = False


_TRUE_WORDS = {"1", "true", "yes", "y", "on"}
_FALSE_WORDS = {"0", "false", "no", "n", "off"}


class Params:
    """Typed, validated access to a loose ``{name: value}`` mapping (CLI/JSON/menu)."""

    def __init__(self, data: Mapping[str, Any] | None = None) -> None:
        self._data: dict[str, Any] = {}
        for key, value in (data or {}).items():
            self._data[str(key).strip().lower().replace("-", "_")] = value

    def names(self) -> set[str]:
        return set(self._data)

    def _fetch(self, key: str) -> Any:
        value = self._data.get(key)
        if value is None or (isinstance(value, str) and value.strip() == ""):
            return None
        return value

    def get_raw(self, key: str, default: Any = None) -> Any:
        value = self._fetch(key)
        return default if value is None else value

    def get_str(self, key: str, default: str | None = None, required: bool = False) -> str | None:
        value = self._fetch(key)
        if value is None:
            if required:
                raise InvalidKeyError(f"Missing required parameter '{key}'.")
            return default
        return str(value)

    def get_int(self, key: str, default: int | None = None, required: bool = False) -> int | None:
        value = self._fetch(key)
        if value is None:
            if required:
                raise InvalidKeyError(f"Missing required integer parameter '{key}'.")
            return default
        return parse_int(value, key)

    def get_bool(self, key: str, default: bool = False) -> bool:
        value = self._fetch(key)
        if value is None:
            return default
        if isinstance(value, bool):
            return value
        word = str(value).strip().lower()
        if word in _TRUE_WORDS:
            return True
        if word in _FALSE_WORDS:
            return False
        raise InvalidKeyError(f"Parameter '{key}' must be true or false (got {value!r}).")

    def get_choice(self, key: str, choices: Sequence[str], default: str) -> str:
        value = self._fetch(key)
        if value is None:
            return default
        word = str(value).strip().lower()
        if word not in choices:
            raise InvalidKeyError(
                f"Parameter '{key}' must be one of: {', '.join(choices)} (got {value!r}).")
        return word

    def reject_unknown(self, allowed: Iterable[str], context: str) -> None:
        allowed_set = set(allowed)
        extra = sorted(self.names() - allowed_set)
        if extra:
            raise InvalidKeyError(
                f"Unknown parameter(s) for {context}: {', '.join(extra)}. "
                f"Allowed: {', '.join(sorted(allowed_set)) or '(none)'}.")


# ============================================================================
# SECTION 4 - CIPHER BASE CLASS & REGISTRY
# ============================================================================

class Cipher(abc.ABC):
    """Common interface of every cipher in the suite."""

    name: ClassVar[str] = ""
    summary: ClassVar[str] = ""
    PARAMS: ClassVar[tuple[ParamSpec, ...]] = ()
    uses_alphabet: ClassVar[bool] = True

    @abc.abstractmethod
    def encrypt(self, text: str) -> str:
        """Return the ciphertext for ``text``."""

    @abc.abstractmethod
    def decrypt(self, text: str) -> str:
        """Return the plaintext for ``text``."""

    @classmethod
    @abc.abstractmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "Cipher":
        """Build an instance from loosely typed parameters."""


CIPHER_REGISTRY: dict[str, type[Cipher]] = {}


def _canon(name: str) -> str:
    """Canonical lookup key: lower-case, accents and separators removed."""
    decomposed = unicodedata.normalize("NFKD", str(name).strip().lower())
    stripped = "".join(c for c in decomposed if not unicodedata.combining(c))
    return re.sub(r"[\s_\-]+", "", stripped)


def register_cipher(*names: str) -> Callable[[type[Cipher]], type[Cipher]]:
    """Class decorator that publishes a cipher under one or more names."""
    def decorator(cls: type[Cipher]) -> type[Cipher]:
        for n in names:
            CIPHER_REGISTRY[_canon(n)] = cls
        return cls
    return decorator


def unique_ciphers() -> list[type[Cipher]]:
    """Registered cipher classes without alias duplicates, in registration order."""
    seen: list[type[Cipher]] = []
    for cls in CIPHER_REGISTRY.values():
        if cls not in seen:
            seen.append(cls)
    return seen


def build_cipher(name: str, params: Mapping[str, Any] | None = None,
                 alphabet: Alphabet | str | None = None, fold: bool = True) -> Cipher:
    """Create a configured cipher by name (the single entry point for CLI/batch)."""
    cls = CIPHER_REGISTRY.get(_canon(name))
    if cls is None:
        available = ", ".join(c.name for c in unique_ciphers())
        raise UnknownCipherError(f"Unknown cipher {name!r}. Available: {available}.")
    data = dict(params or {})
    alpha_param = data.pop("alphabet", None)
    fold_param = data.pop("fold", None)
    if isinstance(alphabet, Alphabet):
        resolved = alphabet
    else:
        if fold_param is not None:
            fold = Params({"fold": fold_param}).get_bool("fold", True)
        resolved = get_alphabet(alphabet if alphabet is not None else alpha_param, fold=fold)
    typed = Params(data)
    typed.reject_unknown([spec.name for spec in cls.PARAMS], cls.name)
    return cls.from_params(typed, resolved)


# ============================================================================
# SECTION 5 - CLASSICAL CIPHERS
# ============================================================================

# ----------------------------------------------------------------------------
# 5.1 Caesar and ROT-N
# ----------------------------------------------------------------------------

@register_cipher("caesar")
class CaesarCipher(Cipher):
    """Shift every letter by a fixed amount, preserving case and other characters."""

    name = "caesar"
    summary = "Shift every letter by a fixed amount (English, Arabic or custom alphabet)."
    PARAMS = (ParamSpec("shift", "Integer shift; negative values shift backwards", default=3),)

    def __init__(self, shift: int, alphabet: Alphabet = ENGLISH) -> None:
        self.alphabet = alphabet
        self.shift = parse_int(shift, "shift") % alphabet.size

    def encrypt(self, text: str) -> str:
        m, s = self.alphabet.size, self.shift
        return self.alphabet.transform(text, lambda i: (i + s) % m)

    def decrypt(self, text: str) -> str:
        m, s = self.alphabet.size, self.shift
        return self.alphabet.transform(text, lambda i: (i - s) % m)

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "CaesarCipher":
        return cls(params.get_int("shift", default=3), alphabet)


@register_cipher("rot", "rotn", "rot13")
class RotNCipher(CaesarCipher):
    """ROT-N: a Caesar shift whose default is half the alphabet (ROT13 for English)."""

    name = "rot"
    summary = "ROT-N rotation; default N is half the alphabet (ROT13 for English)."
    PARAMS = (ParamSpec("n", "Rotation amount N (default: alphabet size / 2)"),)

    def __init__(self, n: int | None = None, alphabet: Alphabet = ENGLISH) -> None:
        super().__init__(alphabet.size // 2 if n is None else n, alphabet)

    @property
    def is_self_inverse(self) -> bool:
        """True when applying the cipher twice returns the original text."""
        return (2 * self.shift) % self.alphabet.size == 0

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "RotNCipher":
        return cls(params.get_int("n"), alphabet)


# ----------------------------------------------------------------------------
# 5.2 Affine
# ----------------------------------------------------------------------------

@register_cipher("affine")
class AffineCipher(Cipher):
    """E(x) = (a*x + b) mod m, with validation that ``a`` is invertible mod m."""

    name = "affine"
    summary = "E(x) = a*x + b (mod m); a must be coprime with the alphabet size."
    PARAMS = (
        ParamSpec("a", "Multiplier, coprime with the alphabet size", default=5),
        ParamSpec("b", "Additive shift", default=8),
    )

    def __init__(self, a: int, b: int, alphabet: Alphabet = ENGLISH) -> None:
        a, b = parse_int(a, "a"), parse_int(b, "b")
        m = alphabet.size
        g = math.gcd(a, m)
        if g != 1:
            raise InvalidKeyError(
                f"Affine multiplier a={a} is invalid: gcd({a}, {m}) = {g}, so it has no "
                f"modular inverse. Valid values of a (mod {m}): {coprime_values(m)}")
        self.alphabet = alphabet
        self.a, self.b = a % m, b % m
        self.a_inverse = mod_inverse(self.a, m)

    def encrypt(self, text: str) -> str:
        m, a, b = self.alphabet.size, self.a, self.b
        return self.alphabet.transform(text, lambda i: (a * i + b) % m)

    def decrypt(self, text: str) -> str:
        m, inv, b = self.alphabet.size, self.a_inverse, self.b
        return self.alphabet.transform(text, lambda i: (inv * (i - b)) % m)

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "AffineCipher":
        return cls(params.get_int("a", 5), params.get_int("b", 8), alphabet)


# ----------------------------------------------------------------------------
# 5.3 Vigenere (repeating key + autokey)
# ----------------------------------------------------------------------------

@register_cipher("vigenere")
class VigenereCipher(Cipher):
    """Polyalphabetic cipher with a repeating key or an autokey stream."""

    MODES: ClassVar[tuple[str, ...]] = ("repeat", "autokey")
    name = "vigenere"
    summary = "Polyalphabetic keyword cipher; modes: repeat (classic) and autokey."
    PARAMS = (
        ParamSpec("key", "Keyword made of letters of the chosen alphabet", required=True),
        ParamSpec("mode", "repeat | autokey", default="repeat"),
    )

    def __init__(self, key: str, mode: str = "repeat", alphabet: Alphabet = ENGLISH) -> None:
        mode = str(mode).strip().lower()
        if mode not in self.MODES:
            raise InvalidKeyError(f"Vigenere mode must be one of {self.MODES} (got {mode!r}).")
        indices = alphabet.indices(str(key))
        if not indices:
            raise InvalidKeyError(
                f"Vigenere key {key!r} contains no letters of the {alphabet.name} alphabet.")
        self.alphabet = alphabet
        self.mode = mode
        self.key_indices = indices
        self.key = alphabet.letters_only(str(key))

    def _run(self, text: str, sign: int) -> str:
        m = self.alphabet.size
        stream = list(self.key_indices)
        out: list[str] = []
        pos = 0
        for ch in text:
            loc = self.alphabet.locate(ch)
            if loc is None:
                out.append(ch)
                continue
            idx, lower = loc
            k = stream[pos % len(stream)] if self.mode == "repeat" else stream[pos]
            result = (idx + sign * k) % m
            if self.mode == "autokey":
                stream.append(idx if sign > 0 else result)  # always the plaintext letter
            out.append(self.alphabet.render(result, lower))
            pos += 1
        return "".join(out)

    def encrypt(self, text: str) -> str:
        return self._run(text, +1)

    def decrypt(self, text: str) -> str:
        return self._run(text, -1)

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "VigenereCipher":
        return cls(params.get_str("key", required=True),
                   params.get_choice("mode", cls.MODES, "repeat"), alphabet)


# ----------------------------------------------------------------------------
# 5.4 Playfair
# ----------------------------------------------------------------------------

@register_cipher("playfair")
class PlayfairCipher(Cipher):
    """Digraph substitution on a 5x5 Latin grid with configurable letter merging.

    Playfair is lossy by design: only A-Z letters survive, output is upper case,
    doubled letters get a filler and odd lengths are padded.  Decryption therefore
    returns the padded letter stream; ``strip_filler`` removes fillers heuristically.
    """

    name = "playfair"
    uses_alphabet = False
    summary = "5x5 digraph cipher (Latin letters only) with configurable I/J merging."
    PARAMS = (
        ParamSpec("key", "Keyword used to build the 5x5 grid", required=True),
        ParamSpec("merge_from", "Letter removed from the grid", default="J"),
        ParamSpec("merge_into", "Letter that replaces the removed one", default="I"),
        ParamSpec("filler", "Letter inserted between doubles / used as padding", default="X"),
        ParamSpec("group_size", "Insert a space every N output letters (0 = off)", default=0),
        ParamSpec("strip_filler", "Heuristically remove fillers when decrypting", default=False),
    )

    def __init__(self, key: str, merge_from: str = "J", merge_into: str = "I",
                 filler: str = "X", group_size: int = 0, strip_filler: bool = False) -> None:
        self.merge_from = self._single_letter(merge_from, "merge_from")
        self.merge_into = self._single_letter(merge_into, "merge_into")
        if self.merge_from == self.merge_into:
            raise InvalidKeyError("merge_from and merge_into must be different letters.")
        self.filler = self._single_letter(filler, "filler")
        self.alt_filler = "Q" if self.filler != "Q" else "Z"
        for letter in (self.filler, self.alt_filler):
            if letter == self.merge_from:
                raise InvalidKeyError(f"Letter {letter!r} is merged away and cannot be a filler.")
        self.group_size = max(0, parse_int(group_size, "group_size"))
        self.strip_filler = bool(strip_filler)
        key_letters = self._prepare(str(key))
        if not key_letters:
            raise InvalidKeyError("Playfair key must contain at least one Latin letter.")
        grid: list[str] = []
        for letter in key_letters + ENGLISH.letters:
            if letter != self.merge_from and letter not in grid:
                grid.append(letter)
        self.matrix = [grid[r * 5:(r + 1) * 5] for r in range(5)]
        self.position = {letter: (r, c) for r, row in enumerate(self.matrix)
                         for c, letter in enumerate(row)}

    @staticmethod
    def _single_letter(value: str, name: str) -> str:
        text = str(value).strip().upper()
        if len(text) != 1 or not ("A" <= text <= "Z"):
            raise InvalidKeyError(f"'{name}' must be a single letter A-Z (got {value!r}).")
        return text

    def _prepare(self, text: str) -> str:
        letters = []
        for ch in text:
            up = ch.upper()
            if len(up) == 1 and "A" <= up <= "Z":
                letters.append(self.merge_into if up == self.merge_from else up)
        return "".join(letters)

    def _filler_for(self, letter: str) -> str:
        return self.filler if letter != self.filler else self.alt_filler

    def _digraphs(self, letters: str) -> list[tuple[str, str]]:
        pairs: list[tuple[str, str]] = []
        i = 0
        while i < len(letters):
            first = letters[i]
            if i + 1 < len(letters) and letters[i + 1] != first:
                pairs.append((first, letters[i + 1]))
                i += 2
            else:  # double letter or dangling last letter
                pairs.append((first, self._filler_for(first)))
                i += 1
        return pairs

    def _shift_pair(self, a: str, b: str, step: int) -> str:
        (ra, ca), (rb, cb) = self.position[a], self.position[b]
        if ra == rb:
            return self.matrix[ra][(ca + step) % 5] + self.matrix[rb][(cb + step) % 5]
        if ca == cb:
            return self.matrix[(ra + step) % 5][ca] + self.matrix[(rb + step) % 5][cb]
        return self.matrix[ra][cb] + self.matrix[rb][ca]

    def _group(self, text: str) -> str:
        if self.group_size <= 0:
            return text
        return " ".join(text[i:i + self.group_size] for i in range(0, len(text), self.group_size))

    def _remove_fillers(self, text: str) -> str:
        fillers = (self.filler, self.alt_filler)
        kept: list[str] = []
        for i, ch in enumerate(text):
            between_doubles = (ch in fillers and i % 2 == 1 and 0 < i < len(text) - 1
                               and text[i - 1] == text[i + 1])
            trailing_pad = ch in fillers and i == len(text) - 1 and i % 2 == 1
            if not (between_doubles or trailing_pad):
                kept.append(ch)
        return "".join(kept)

    def encrypt(self, text: str) -> str:
        letters = self._prepare(text)
        pairs = self._digraphs(letters)
        return self._group("".join(self._shift_pair(a, b, +1) for a, b in pairs))

    def decrypt(self, text: str) -> str:
        letters = self._prepare(text)
        if len(letters) % 2:
            raise InvalidInputError(
                f"Playfair ciphertext needs an even number of letters (got {len(letters)}).")
        pairs = [(letters[i], letters[i + 1]) for i in range(0, len(letters), 2)]
        plain = "".join(self._shift_pair(a, b, -1) for a, b in pairs)
        return self._remove_fillers(plain) if self.strip_filler else plain

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "PlayfairCipher":
        if alphabet.letters != ENGLISH.letters:
            raise InvalidKeyError("Playfair supports only the 26-letter Latin alphabet.")
        return cls(params.get_str("key", required=True),
                   merge_from=params.get_str("merge_from", "J"),
                   merge_into=params.get_str("merge_into", "I"),
                   filler=params.get_str("filler", "X"),
                   group_size=params.get_int("group_size", 0),
                   strip_filler=params.get_bool("strip_filler", False))


# ----------------------------------------------------------------------------
# 5.5 Columnar transposition
# ----------------------------------------------------------------------------

@register_cipher("columnar", "transposition")
class ColumnarTranspositionCipher(Cipher):
    """Write the text in rows under a keyword, read the columns in key order.

    Works on every character (spaces and punctuation included), so with
    ``padding='none'`` the round trip is exact.  ``pad`` fills the last row;
    ``pad_unpad`` also strips up to ``len(key)-1`` trailing pad characters when
    decrypting (ambiguous if the plaintext really ends with the pad character).
    """

    PADDING_MODES: ClassVar[tuple[str, ...]] = ("none", "pad", "pad_unpad")
    name = "columnar"
    uses_alphabet = False
    summary = "Keyed columnar transposition with optional padding / unpadding."
    PARAMS = (
        ParamSpec("key", "Keyword (alphabetical order) or numeric order like '3 1 4 2'",
                  required=True),
        ParamSpec("padding", "none | pad | pad_unpad", default="none"),
        ParamSpec("pad_char", "Padding character", default="X"),
    )

    def __init__(self, key: str, padding: str = "none", pad_char: str = "X") -> None:
        padding = str(padding).strip().lower()
        if padding not in self.PADDING_MODES:
            raise InvalidKeyError(f"padding must be one of {self.PADDING_MODES} (got {padding!r}).")
        if len(str(pad_char)) != 1:
            raise InvalidKeyError("pad_char must be exactly one character.")
        self.order = self.column_order(str(key))
        self.padding = padding
        self.pad_char = str(pad_char)

    @staticmethod
    def column_order(key: str) -> list[int]:
        """Column indices in the order they are read out."""
        tokens = [t for t in re.split(r"[\s,;]+", key.strip()) if t]
        if len(tokens) > 1 and all(t.isdigit() for t in tokens):
            ranks = [int(t) for t in tokens]
            if sorted(ranks) != list(range(1, len(ranks) + 1)):
                raise InvalidKeyError(
                    f"A numeric key must be a permutation of 1..{len(ranks)} (got {key!r}).")
            return sorted(range(len(ranks)), key=lambda i: ranks[i])
        chars = [c for c in key if not c.isspace()]
        if len(chars) < 2:
            raise InvalidKeyError("Columnar key needs at least two characters.")
        folded = [c.casefold() for c in chars]
        return sorted(range(len(chars)), key=lambda i: (folded[i], i))

    def encrypt(self, text: str) -> str:
        n = len(self.order)
        if self.padding != "none" and text and len(text) % n:
            text += self.pad_char * (n - len(text) % n)
        return "".join(text[c::n] for c in self.order)

    def decrypt(self, text: str) -> str:
        n, total = len(self.order), len(text)
        full_rows, remainder = divmod(total, n)
        lengths = [full_rows + (1 if j < remainder else 0) for j in range(n)]
        columns = [""] * n
        cursor = 0
        for col in self.order:
            columns[col] = text[cursor:cursor + lengths[col]]
            cursor += lengths[col]
        rows = ("".join(columns[j][r] for j in range(n) if r < len(columns[j]))
                for r in range(full_rows + (1 if remainder else 0)))
        plain = "".join(rows)
        if self.padding == "pad_unpad":
            removed = 0
            while plain.endswith(self.pad_char) and removed < n - 1:
                plain = plain[:-1]
                removed += 1
        return plain

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "ColumnarTranspositionCipher":
        return cls(params.get_str("key", required=True),
                   params.get_choice("padding", cls.PADDING_MODES, "none"),
                   params.get_str("pad_char", "X"))


# ----------------------------------------------------------------------------
# 5.6 XOR (repeating key / hash-based stream)
# ----------------------------------------------------------------------------

@register_cipher("xor")
class XorCipher(Cipher):
    """XOR the UTF-8 bytes of the text with a repeating key or a SHA-256 keystream.

    Ciphertext is rendered as hex, Base64 or (only if the bytes happen to form
    valid UTF-8) plain text.  The ``stream`` mode derives keystream blocks as
    SHA-256(key || counter) - a teaching construction, not a vetted cipher.
    """

    FORMATS: ClassVar[tuple[str, ...]] = ("hex", "base64", "utf8")
    KEY_FORMATS: ClassVar[tuple[str, ...]] = ("text", "hex")
    MODES: ClassVar[tuple[str, ...]] = ("repeat", "stream")
    name = "xor"
    uses_alphabet = False
    summary = "XOR with a repeating key or hash keystream; hex / base64 / utf8 output."
    PARAMS = (
        ParamSpec("key", "Key text (or hex digits when key_format=hex)", required=True),
        ParamSpec("key_format", "text | hex", default="text"),
        ParamSpec("mode", "repeat | stream", default="repeat"),
        ParamSpec("format", "hex | base64 | utf8 (ciphertext representation)", default="hex"),
    )

    def __init__(self, key: str, key_format: str = "text", mode: str = "repeat",
                 output_format: str = "hex") -> None:
        for value, choices, label in ((key_format, self.KEY_FORMATS, "key_format"),
                                      (mode, self.MODES, "mode"),
                                      (output_format, self.FORMATS, "format")):
            if value not in choices:
                raise InvalidKeyError(f"{label} must be one of {choices} (got {value!r}).")
        if key_format == "hex":
            try:
                self.key = bytes.fromhex(re.sub(r"\s+", "", str(key)))
            except ValueError:
                raise InvalidKeyError(f"XOR key is not valid hex: {key!r}") from None
        else:
            self.key = str(key).encode("utf-8")
        if not self.key:
            raise InvalidKeyError("XOR key must not be empty.")
        self.mode = mode
        self.output_format = output_format

    @staticmethod
    def xor_bytes(data: bytes, keystream: bytes) -> bytes:
        return bytes(a ^ b for a, b in zip(data, keystream))

    def keystream(self, length: int) -> bytes:
        if self.mode == "repeat":
            repeats = -(-length // len(self.key))
            return (self.key * repeats)[:length]
        stream = bytearray()
        counter = 0
        while len(stream) < length:
            stream += hashlib.sha256(self.key + counter.to_bytes(8, "big")).digest()
            counter += 1
        return bytes(stream[:length])

    @staticmethod
    def parse_bytes(text: str, fmt: str) -> bytes:
        """Decode ciphertext text in ``fmt`` (hex / base64 / utf8) into raw bytes."""
        if fmt == "utf8":
            return text.encode("utf-8")
        compact = re.sub(r"\s+", "", text)
        if not compact:
            raise InvalidInputError("Ciphertext is empty.")
        if fmt == "hex":
            if compact.lower().startswith("0x"):
                compact = compact[2:]
            try:
                return bytes.fromhex(compact)
            except ValueError:
                raise EncodingFormatError(
                    "Input is not valid hex (expected an even number of 0-9a-f digits).") from None
        if fmt == "base64":
            try:
                return base64.b64decode(compact + "=" * (-len(compact) % 4), validate=True)
            except (binascii.Error, ValueError):
                raise EncodingFormatError("Input is not valid Base64.") from None
        raise InvalidKeyError(f"Unknown format {fmt!r}.")

    def _emit(self, data: bytes) -> str:
        if self.output_format == "hex":
            return data.hex()
        if self.output_format == "base64":
            return base64.b64encode(data).decode("ascii")
        try:
            return data.decode("utf-8")
        except UnicodeDecodeError:
            raise EncodingFormatError(
                "XOR output is not valid UTF-8 text; use format=hex or format=base64.") from None

    def encrypt(self, text: str) -> str:
        try:
            data = text.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise InvalidInputError(f"Text cannot be encoded as UTF-8: {exc}") from None
        return self._emit(self.xor_bytes(data, self.keystream(len(data))))

    def decrypt(self, text: str) -> str:
        data = self.parse_bytes(text, self.output_format)
        plain = self.xor_bytes(data, self.keystream(len(data)))
        try:
            return plain.decode("utf-8")
        except UnicodeDecodeError:
            raise EncodingFormatError(
                "Decrypted bytes are not valid UTF-8: wrong key, mode or input format?") from None

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "XorCipher":
        return cls(params.get_str("key", required=True),
                   params.get_choice("key_format", cls.KEY_FORMATS, "text"),
                   params.get_choice("mode", cls.MODES, "repeat"),
                   params.get_choice("format", cls.FORMATS, "hex"))


# ============================================================================
# SECTION 6 - ENIGMA-STYLE ROTOR MACHINE
# ============================================================================

_A = ord("A")

# (wiring, turnover notches) of the historical Enigma I / M3 rotors.
_ROTOR_TABLE = {
    "I": ("EKMFLGDQVZNTOWYHXUSPAIBRCJ", "Q"),
    "II": ("AJDKSIRUXBLHWTMCQGZNPYFVOE", "E"),
    "III": ("BDFHJLCPRTXVZNYEIWGAKMUSQO", "V"),
    "IV": ("ESOVPZJAYQUIRHXLNFTGKDCMWB", "J"),
    "V": ("VZBRGITYUPSDNHLXAWMJQOFECK", "Z"),
    "VI": ("JPGVOUMFYQBENHZRDKASXLICTW", "ZM"),
    "VII": ("NZJHGRCXMYSWBOUFAIVLPEKQDT", "ZM"),
    "VIII": ("FKQHTLXOCBJSPDZRAMEWNIUYGV", "ZM"),
}
REFLECTOR_TABLE = {
    "A": "EJMZALYXVBWFCRQUONTSPIKHGD",
    "B": "YRUHQSLDPXNGOKMIEBFZCWVJAT",
    "C": "FVPJIAOYEDRZXWGCTKUQSBNMHL",
}


def _is_permutation(wiring: str) -> bool:
    return len(wiring) == 26 and sorted(wiring) == list(ENGLISH.letters)


@dataclass(frozen=True)
class RotorSpec:
    """Wiring and turnover notch(es) of one rotor."""
    name: str
    wiring: str
    notches: str = ""

    def __post_init__(self) -> None:
        if not _is_permutation(self.wiring):
            raise InvalidKeyError(
                f"Rotor {self.name!r}: wiring must be a permutation of A-Z (26 letters).")
        if any(n not in ENGLISH.letters for n in self.notches):
            raise InvalidKeyError(f"Rotor {self.name!r}: notches must be letters A-Z.")


ROTORS: dict[str, RotorSpec] = {n: RotorSpec(n, w, notch) for n, (w, notch) in _ROTOR_TABLE.items()}


def resolve_rotor(token: str) -> RotorSpec:
    """Rotor by name (I-VIII, or 1-8) or custom ``WIRING[:NOTCHES]``."""
    text = str(token).strip().upper()
    if ":" in text or len(text) == 26:
        wiring, _, notches = text.partition(":")
        return RotorSpec("CUSTOM", wiring, notches)
    if text.isdigit() and 1 <= int(text) <= 8:
        text = list(ROTORS)[int(text) - 1]
    if text not in ROTORS:
        raise InvalidKeyError(
            f"Unknown rotor {token!r}. Use {', '.join(ROTORS)} or a custom 'WIRING:NOTCH'.")
    return ROTORS[text]


def resolve_reflector(token: str) -> str:
    """Reflector wiring by name (A, B, C) or a custom 26-letter involution."""
    text = str(token).strip().upper()
    wiring = REFLECTOR_TABLE.get(text, text)
    if not _is_permutation(wiring):
        raise InvalidKeyError(
            f"Unknown reflector {token!r}. Use {', '.join(REFLECTOR_TABLE)} or 26 custom letters.")
    for i, ch in enumerate(wiring):
        target = ord(ch) - _A
        if target == i or wiring[target] != ENGLISH.letters[i]:
            raise InvalidKeyError(
                "A reflector must pair letters symmetrically with no letter mapping to itself.")
    return wiring


def _split_tokens(value: Any, *, split_letters: bool) -> list[str]:
    """Split ``'I II III'``, ``'I,II,III'`` or a list; optionally explode ``'ABC'``."""
    if isinstance(value, (list, tuple)):
        return [str(v).strip() for v in value if str(v).strip()]
    text = str(value).strip()
    if not text:
        return []
    if re.search(r"[\s,;]", text):
        return [t for t in re.split(r"[\s,;]+", text) if t]
    return list(text) if split_letters else [text]


def _parse_setting(token: str, what: str) -> int:
    """Parse a ring/position given as a letter A-Z or a number 1-26 -> 0..25."""
    text = str(token).strip().upper()
    if text.isdigit():
        number = int(text)
        if not 1 <= number <= 26:
            raise InvalidKeyError(f"{what} number must be between 1 and 26 (got {token}).")
        return number - 1
    if len(text) == 1 and "A" <= text <= "Z":
        return ord(text) - _A
    raise InvalidKeyError(f"Invalid {what} {token!r}: use a letter A-Z or a number 1-26.")


def parse_plugboard(value: Any) -> list[tuple[int, int]]:
    """Parse ``'AB CD EF'`` (or ``'ABCDEF'``) into validated letter-index pairs."""
    tokens = _split_tokens(value, split_letters=False)
    if len(tokens) == 1 and len(tokens[0]) > 2 and len(tokens[0]) % 2 == 0 and tokens[0].isalpha():
        tokens = [tokens[0][i:i + 2] for i in range(0, len(tokens[0]), 2)]
    pairs: list[tuple[int, int]] = []
    used: set[str] = set()
    for token in tokens:
        pair = token.upper()
        if len(pair) != 2 or not pair.isalpha() or not pair.isascii():
            raise InvalidKeyError(f"Invalid plugboard pair {token!r}: use two letters like 'AB'.")
        if pair[0] == pair[1]:
            raise InvalidKeyError(f"Plugboard pair {token!r} connects a letter to itself.")
        for letter in pair:
            if letter in used:
                raise InvalidKeyError(f"Letter {letter} appears more than once in the plugboard.")
            used.add(letter)
        pairs.append((ord(pair[0]) - _A, ord(pair[1]) - _A))
    return pairs


class Rotor:
    """One rotating wheel with ring setting (Ringstellung) and current position."""

    def __init__(self, spec: RotorSpec, ring: int = 0, position: int = 0) -> None:
        self.spec = spec
        self.ring = ring % 26
        self.position = position % 26
        self._forward = [ord(c) - _A for c in spec.wiring]
        self._backward = [0] * 26
        for i, out in enumerate(self._forward):
            self._backward[out] = i
        self._notches = {ord(c) - _A for c in spec.notches}

    @property
    def at_notch(self) -> bool:
        return self.position in self._notches

    def step(self) -> None:
        self.position = (self.position + 1) % 26

    def forward(self, contact: int) -> int:
        offset = self.position - self.ring
        return (self._forward[(contact + offset) % 26] - offset) % 26

    def backward(self, contact: int) -> int:
        offset = self.position - self.ring
        return (self._backward[(contact + offset) % 26] - offset) % 26


class EnigmaMachine:
    """Stateful three-rotor Enigma (left, middle, right) with double stepping."""

    def __init__(self, specs: Sequence[RotorSpec], reflector: str, rings: Sequence[int],
                 positions: Sequence[int], plugs: Sequence[tuple[int, int]] = ()) -> None:
        if not (len(specs) == len(rings) == len(positions) == 3):
            raise InvalidKeyError(
                "This simulator models a 3-rotor Enigma: give exactly 3 rotors, 3 ring "
                "settings and 3 start positions (left to right).")
        self.rotors = [Rotor(s, r, p) for s, r, p in zip(specs, rings, positions)]
        self.reflector = [ord(c) - _A for c in reflector]
        self.plugboard = list(range(26))
        for a, b in plugs:
            self.plugboard[a], self.plugboard[b] = b, a

    @property
    def positions(self) -> str:
        return "".join(chr(r.position + _A) for r in self.rotors)

    def _step(self) -> None:
        left, middle, right = self.rotors
        if middle.at_notch:      # double step: middle moves and drags the left rotor
            middle.step()
            left.step()
        elif right.at_notch:
            middle.step()
        right.step()

    def press(self, letter: int) -> int:
        """Encipher one letter (0..25), stepping the rotors first."""
        self._step()
        signal = self.plugboard[letter]
        for rotor in reversed(self.rotors):
            signal = rotor.forward(signal)
        signal = self.reflector[signal]
        for rotor in self.rotors:
            signal = rotor.backward(signal)
        return self.plugboard[signal]

    def process(self, text: str, preserve_case: bool = True) -> str:
        out: list[str] = []
        for ch in text:
            if ch.isascii() and ch.isalpha():
                enciphered = chr(self.press(ord(ch.upper()) - _A) + _A)
                out.append(enciphered.lower() if preserve_case and ch.islower() else enciphered)
            else:
                out.append(ch)
        return "".join(out)


@register_cipher("enigma")
class EnigmaCipher(Cipher):
    """Stateless wrapper: every call starts from the configured initial settings.

    Enigma is reciprocal, so ``decrypt`` is the same operation as ``encrypt``.
    """

    name = "enigma"
    uses_alphabet = False
    summary = "Educational 3-rotor Enigma: rotors I-VIII, reflectors A/B/C, rings, plugboard."
    PARAMS = (
        ParamSpec("rotors", "Left-to-right rotors, e.g. 'I II III' (or 'WIRING:NOTCH')",
                  default="I II III"),
        ParamSpec("reflector", "A | B | C or 26 custom letters", default="B"),
        ParamSpec("rings", "Ring settings, letters or 1-26, e.g. 'A A A'", default="A A A"),
        ParamSpec("positions", "Start positions, letters or 1-26, e.g. 'A D U'",
                  default="A A A"),
        ParamSpec("plugboard", "Steckerbrett pairs, e.g. 'AB CD EF'", default=""),
        ParamSpec("preserve_case", "Keep lower-case letters lower-case", default=True),
    )

    def __init__(self, rotors: Any = "I II III", reflector: str = "B", rings: Any = "A A A",
                 positions: Any = "A A A", plugboard: Any = "", preserve_case: bool = True) -> None:
        self.specs = tuple(resolve_rotor(t) for t in _split_tokens(rotors, split_letters=False))
        self.reflector = resolve_reflector(reflector)
        self.rings = tuple(_parse_setting(t, "ring setting")
                           for t in _split_tokens(rings, split_letters=True))
        self.positions = tuple(_parse_setting(t, "start position")
                               for t in _split_tokens(positions, split_letters=True))
        self.plugs = tuple(parse_plugboard(plugboard))
        self.preserve_case = bool(preserve_case)
        self.new_machine()  # validates the whole configuration immediately

    def new_machine(self) -> EnigmaMachine:
        return EnigmaMachine(self.specs, self.reflector, self.rings, self.positions, self.plugs)

    def encrypt(self, text: str) -> str:
        return self.new_machine().process(text, self.preserve_case)

    def decrypt(self, text: str) -> str:
        return self.encrypt(text)

    @classmethod
    def from_params(cls, params: Params, alphabet: Alphabet) -> "EnigmaCipher":
        if alphabet.letters != ENGLISH.letters:
            raise InvalidKeyError("The Enigma simulator supports only the Latin alphabet A-Z.")
        return cls(params.get_raw("rotors", "I II III"), params.get_str("reflector", "B"),
                   params.get_raw("rings", "A A A"), params.get_raw("positions", "A A A"),
                   params.get_raw("plugboard", ""), params.get_bool("preserve_case", True))


# ============================================================================
# SECTION 7 - CRYPTANALYSIS
# ============================================================================

ENGLISH_FREQUENCIES = {
    "A": 8.167, "B": 1.492, "C": 2.782, "D": 4.253, "E": 12.702, "F": 2.228,
    "G": 2.015, "H": 6.094, "I": 6.966, "J": 0.153, "K": 0.772, "L": 4.025,
    "M": 2.406, "N": 6.749, "O": 7.507, "P": 1.929, "Q": 0.095, "R": 5.987,
    "S": 6.327, "T": 9.056, "U": 2.758, "V": 0.978, "W": 2.360, "X": 0.150,
    "Y": 1.974, "Z": 0.074,
}

# Approximate relative frequencies for Modern Standard Arabic text after letter
# folding (values are normalised on load).  Replace them with a profile built
# from your own corpus via FrequencyProfile.from_text() / --reference for
# sharper results.
ARABIC_FREQUENCIES = {
    "ا": 12.3, "ل": 11.5, "ي": 7.4, "م": 5.9, "و": 5.5, "ن": 5.4, "ر": 4.8,
    "ت": 4.5, "ب": 4.2, "ع": 3.9, "ه": 5.0, "د": 3.0, "ف": 2.9, "ك": 2.8,
    "ق": 2.7, "س": 2.7, "ح": 2.4, "ج": 1.7, "ش": 1.2, "ط": 1.1, "ص": 1.1,
    "خ": 1.0, "ز": 0.7, "ض": 0.8, "ذ": 0.7, "ث": 0.6, "غ": 0.6, "ظ": 0.3,
}

_MIN_PROBABILITY = 1e-4  # smoothing so chi-squared never divides by zero


class FrequencyProfile:
    """Expected letter probabilities of a language over a given alphabet."""

    def __init__(self, alphabet: Alphabet, probabilities: Sequence[float],
                 name: str = "custom", is_uniform: bool = False) -> None:
        if len(probabilities) != alphabet.size:
            raise AnalysisError("A frequency profile needs one value per alphabet letter.")
        total = float(sum(probabilities))
        if total <= 0 or any(p < 0 for p in probabilities):
            raise AnalysisError("Frequencies must be non-negative and not all zero.")
        smoothed = [max(p / total, _MIN_PROBABILITY) for p in probabilities]
        norm = sum(smoothed)
        self.alphabet = alphabet
        self.name = name
        self.is_uniform = is_uniform
        self.probs = [p / norm for p in smoothed]

    @property
    def expected_ioc(self) -> float:
        """Index of coincidence expected for text drawn from this profile."""
        return sum(p * p for p in self.probs)

    @classmethod
    def from_mapping(cls, alphabet: Alphabet, mapping: Mapping[str, float],
                     name: str = "custom") -> "FrequencyProfile":
        unknown = [k for k in mapping if k not in alphabet.letters]
        if unknown:
            raise AnalysisError(f"Profile letters not in the alphabet: {''.join(unknown)!r}")
        return cls(alphabet, [mapping.get(ch, 0.0) for ch in alphabet.letters], name)

    @classmethod
    def uniform(cls, alphabet: Alphabet) -> "FrequencyProfile":
        return cls(alphabet, [1.0] * alphabet.size, name="uniform", is_uniform=True)

    @classmethod
    def from_text(cls, alphabet: Alphabet, text: str, name: str = "reference") -> "FrequencyProfile":
        counts = letter_counts(text, alphabet)
        if sum(counts) < 30:
            raise AnalysisError("Reference text needs at least 30 letters of the chosen alphabet.")
        return cls(alphabet, counts, name=name)

    @classmethod
    def for_alphabet(cls, alphabet: Alphabet) -> "FrequencyProfile":
        """Built-in profile for English/Arabic, otherwise a uniform fallback."""
        if alphabet.letters == ENGLISH.letters:
            return cls.from_mapping(alphabet, ENGLISH_FREQUENCIES, "english")
        if alphabet.letters == ARABIC.letters:
            return cls.from_mapping(alphabet, ARABIC_FREQUENCIES, "arabic")
        return cls.uniform(alphabet)


def letter_counts(text: str, alphabet: Alphabet) -> list[int]:
    counts = [0] * alphabet.size
    for idx in alphabet.indices(text):
        counts[idx] += 1
    return counts


def index_of_coincidence(counts: Sequence[int]) -> float:
    """Probability that two randomly drawn letters of the sample are equal."""
    n = sum(counts)
    if n < 2:
        return 0.0
    return sum(c * (c - 1) for c in counts) / (n * (n - 1))


def chi_squared(counts: Sequence[int], profile: FrequencyProfile) -> float:
    """Pearson chi-squared distance between observed counts and the profile."""
    n = sum(counts)
    if n == 0:
        return math.inf
    return sum((c - n * p) ** 2 / (n * p) for c, p in zip(counts, profile.probs))


def shannon_entropy(counts: Sequence[int]) -> float:
    """Entropy of the letter distribution in bits per letter."""
    n = sum(counts)
    return -sum((c / n) * math.log2(c / n) for c in counts if c) if n else 0.0


def reduce_repeating_key(key: Any) -> Any:
    """Shorten ``key`` to its smallest period (works for str and bytes)."""
    n = len(key)
    for period in range(1, n + 1):
        if n % period == 0 and key == key[:period] * (n // period):
            return key[:period]
    return key


def describe_key(key: Any) -> str:
    if isinstance(key, tuple) and len(key) == 2:
        return f"a={key[0]}, b={key[1]}"
    if isinstance(key, (bytes, bytearray)):
        printable = key.decode("ascii", errors="ignore")
        text = f" '{printable}'" if printable.isprintable() and len(printable) == len(key) else ""
        return key.hex() + text
    return str(key)


@dataclass
class Candidate:
    """One decryption hypothesis with its statistical fit (lower chi2 = better)."""
    key: Any
    plaintext: str
    chi2: float
    ioc: float
    rank: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {"rank": self.rank, "key": describe_key(self.key),
                "chi2": round(self.chi2, 2) if math.isfinite(self.chi2) else None,
                "ioc": round(self.ioc, 4), "plaintext": self.plaintext}


def _require_letters(text: str, alphabet: Alphabet, minimum: int = 1) -> int:
    count = len(alphabet.indices(text))
    if count < minimum:
        raise AnalysisError(
            f"Need at least {minimum} letter(s) of the '{alphabet.name}' alphabet "
            f"(found {count}). Check the --alphabet option.")
    return count


def rank_candidates(pairs: Iterable[tuple[Any, str]], alphabet: Alphabet,
                    profile: FrequencyProfile, top: int | None = None) -> list[Candidate]:
    """Score ``(key, plaintext)`` pairs and return them best-first."""
    scored = []
    for key, plaintext in pairs:
        counts = letter_counts(plaintext, alphabet)
        scored.append(Candidate(key, plaintext, chi_squared(counts, profile),
                                index_of_coincidence(counts)))
    scored.sort(key=lambda c: (c.chi2, -c.ioc))
    for position, cand in enumerate(scored, 1):
        cand.rank = position
    return scored[:top] if top else scored


# ----------------------------------------------------------------------------
# 7.1 Brute force
# ----------------------------------------------------------------------------

def brute_force_caesar(ciphertext: str, alphabet: Alphabet = ENGLISH,
                       profile: FrequencyProfile | None = None,
                       top: int | None = None) -> list[Candidate]:
    """Try every shift and rank the results by chi-squared fit."""
    _require_letters(ciphertext, alphabet)
    profile = profile or FrequencyProfile.for_alphabet(alphabet)
    pairs = ((s, CaesarCipher(s, alphabet).decrypt(ciphertext)) for s in range(alphabet.size))
    return rank_candidates(pairs, alphabet, profile, top)


def brute_force_affine(ciphertext: str, alphabet: Alphabet = ENGLISH,
                       profile: FrequencyProfile | None = None,
                       top: int | None = None) -> list[Candidate]:
    """Try every valid ``(a, b)`` pair (phi(m) * m keys) and rank the results."""
    _require_letters(ciphertext, alphabet)
    profile = profile or FrequencyProfile.for_alphabet(alphabet)
    m = alphabet.size
    pairs = (((a, b), AffineCipher(a, b, alphabet).decrypt(ciphertext))
             for a in coprime_values(m) for b in range(m))
    return rank_candidates(pairs, alphabet, profile, top)


# ----------------------------------------------------------------------------
# 7.2 Key-length estimation (Kasiski + IoC) and the Vigenere breaker
# ----------------------------------------------------------------------------

@dataclass
class KasiskiResult:
    """Repeated n-grams, their spacings and the factor votes they produce."""
    repeats: list[tuple[str, list[int]]]
    spacings: list[int]
    factor_votes: Counter

    def ranked_lengths(self, top: int | None = None) -> list[tuple[int, int]]:
        ranked = sorted(self.factor_votes.items(), key=lambda kv: (-kv[1], kv[0]))
        return ranked[:top] if top else ranked


def kasiski_examination(ciphertext: str, alphabet: Alphabet = ENGLISH, min_ngram: int = 3,
                        max_ngram: int = 5, max_key_len: int = 20) -> KasiskiResult:
    """Find repeated n-grams; spacings between repeats are multiples of the key length."""
    if min_ngram < 2 or max_ngram < min_ngram:
        raise AnalysisError("Require 2 <= min_ngram <= max_ngram.")
    stream = alphabet.letters_only(ciphertext)
    repeats: list[tuple[str, list[int]]] = []
    spacings: list[int] = []
    votes: Counter = Counter()
    for n in range(max_ngram, min_ngram - 1, -1):
        seen: dict[str, list[int]] = defaultdict(list)
        for i in range(len(stream) - n + 1):
            seen[stream[i:i + n]].append(i)
        weight = n - min_ngram + 1  # longer repeats are less likely to be coincidences
        for gram, positions in seen.items():
            if len(positions) < 2:
                continue
            repeats.append((gram, positions))
            for first, second in zip(positions, positions[1:]):
                gap = second - first
                spacings.append(gap)
                for factor in range(2, max_key_len + 1):
                    if gap % factor == 0:
                        votes[factor] += weight
    repeats.sort(key=lambda item: (-len(item[0]), -len(item[1])))
    return KasiskiResult(repeats, spacings, votes)


@dataclass
class KeyLengthEstimate:
    length: int
    avg_ioc: float
    kasiski_votes: int
    rank: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {"rank": self.rank, "length": self.length,
                "avg_ioc": round(self.avg_ioc, 4), "kasiski_votes": self.kasiski_votes}


def estimate_key_length(ciphertext: str, alphabet: Alphabet = ENGLISH,
                        profile: FrequencyProfile | None = None,
                        max_len: int = 20) -> list[KeyLengthEstimate]:
    """Rank candidate key lengths.

    For each length k the text is split into k columns and their IoC values are
    averaged.  Lengths whose average reaches 85% of the best value are "plausible";
    among them the shortest comes first (multiples of the true length look equally
    good).  Kasiski factor votes are reported as independent supporting evidence.
    """
    letters = alphabet.indices(ciphertext)
    if len(letters) < 10:
        raise AnalysisError("Need at least 10 letters to estimate a key length.")
    max_len = max(1, min(int(max_len), len(letters) // 4))
    kasiski = kasiski_examination(ciphertext, alphabet, max_key_len=max_len)
    estimates: list[KeyLengthEstimate] = []
    for k in range(1, max_len + 1):
        column_iocs = []
        for start in range(k):
            counts = [0] * alphabet.size
            for value in letters[start::k]:
                counts[value] += 1
            column_iocs.append(index_of_coincidence(counts))
        estimates.append(KeyLengthEstimate(k, sum(column_iocs) / k, kasiski.factor_votes.get(k, 0)))
    threshold = 0.85 * max(e.avg_ioc for e in estimates)
    plausible = sorted((e for e in estimates if e.avg_ioc >= threshold), key=lambda e: e.length)
    others = sorted((e for e in estimates if e.avg_ioc < threshold), key=lambda e: -e.avg_ioc)
    ranked = plausible + others
    for position, estimate in enumerate(ranked, 1):
        estimate.rank = position
    return ranked


def _best_shift(counts: Sequence[int], profile: FrequencyProfile) -> int:
    """Caesar shift of one Vigenere column that best matches the profile."""
    m = len(counts)
    best_shift, best_score = 0, math.inf
    for shift in range(m):
        rotated = [counts[(j + shift) % m] for j in range(m)]
        score = chi_squared(rotated, profile)
        if score < best_score:
            best_shift, best_score = shift, score
    return best_shift


def break_vigenere(ciphertext: str, alphabet: Alphabet = ENGLISH,
                   profile: FrequencyProfile | None = None, key_length: int | None = None,
                   max_key_length: int = 20, top: int = 3) -> list[Candidate]:
    """Recover repeating-key Vigenere keys (autokey is not covered).

    Candidate key lengths come from :func:`estimate_key_length` (or the explicit
    ``key_length``); every column is solved as a Caesar cipher by chi-squared and the
    complete decryptions are ranked.
    """
    profile = profile or FrequencyProfile.for_alphabet(alphabet)
    letters = alphabet.indices(ciphertext)
    if len(letters) < 20:
        raise AnalysisError("Need at least 20 letters to break a Vigenere cipher.")
    if key_length is not None:
        if key_length < 1 or key_length > len(letters):
            raise InvalidKeyError("key_length must be between 1 and the number of letters.")
        lengths = [key_length]
    else:
        lengths = [e.length for e in
                   estimate_key_length(ciphertext, alphabet, profile, max_key_length)[:3]]
    results: dict[str, str] = {}
    for k in lengths:
        key_chars = []
        for start in range(k):
            counts = [0] * alphabet.size
            for value in letters[start::k]:
                counts[value] += 1
            key_chars.append(alphabet.letters[_best_shift(counts, profile)])
        key = reduce_repeating_key("".join(key_chars))
        if key not in results:
            results[key] = VigenereCipher(key, "repeat", alphabet).decrypt(ciphertext)
    return rank_candidates(results.items(), alphabet, profile, top)


# ----------------------------------------------------------------------------
# 7.3 XOR cryptanalysis (single-byte brute force, repeating-key breaker)
# ----------------------------------------------------------------------------

def _build_byte_scores() -> list[float]:
    """Per-byte plausibility weights for English text (higher = more plausible)."""
    table = [-25.0] * 256
    for b in range(32, 127):
        table[b] = 0.5
    for letter, percent in ENGLISH_FREQUENCIES.items():
        table[ord(letter.lower())] = percent
        table[ord(letter)] = percent / 4
    table[ord(" ")] = 19.0
    for b in b"\t\r\n":
        table[b] = 1.0
    for b in b".,'\"-!?;:":
        table[b] = 1.5
    return table


_BYTE_SCORES = _build_byte_scores()


def score_english_bytes(data: bytes) -> float:
    """Average plausibility of ``data`` as English text (higher is better)."""
    return sum(_BYTE_SCORES[b] for b in data) / max(1, len(data))


@dataclass
class XorCandidate:
    key: bytes
    plaintext: str
    score: float
    rank: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {"rank": self.rank, "key": describe_key(self.key),
                "score": round(self.score, 3), "plaintext": self.plaintext}


def _xor_byte_ranking(data: bytes) -> list[tuple[float, int]]:
    ranked = [(score_english_bytes(bytes(b ^ k for b in data)), k) for k in range(256)]
    ranked.sort(key=lambda item: -item[0])
    return ranked


def brute_force_xor_single_byte(data: bytes, top: int | None = None) -> list[XorCandidate]:
    """Try all 256 single-byte keys and rank by English plausibility."""
    if not data:
        raise AnalysisError("No ciphertext bytes to analyse.")
    out = []
    for position, (score, k) in enumerate(_xor_byte_ranking(data), 1):
        plain = bytes(b ^ k for b in data).decode("utf-8", errors="replace")
        out.append(XorCandidate(bytes([k]), plain, score, position))
    return out[:top] if top else out


def hamming_distance(a: bytes, b: bytes) -> int:
    """Number of differing bits between two byte strings."""
    return sum(bin(x ^ y).count("1") for x, y in zip(a, b))


def estimate_xor_key_sizes(data: bytes, max_size: int = 40, top: int = 4) -> list[tuple[int, float]]:
    """Rank key sizes by normalised Hamming distance between consecutive blocks."""
    max_size = min(max_size, len(data) // 4)
    scored: list[tuple[int, float]] = []
    for k in range(2, max_size + 1):
        blocks = [data[i:i + k] for i in range(0, len(data) - k + 1, k)][:12]
        if len(blocks) < 2:
            continue
        distances = [hamming_distance(blocks[i], blocks[j]) / k
                     for i in range(len(blocks)) for j in range(i + 1, len(blocks))]
        scored.append((k, sum(distances) / len(distances)))
    scored.sort(key=lambda item: item[1])
    return scored[:top]


def break_repeating_xor(data: bytes, key_size: int | None = None, max_size: int = 40,
                        top: int = 3) -> list[XorCandidate]:
    """Recover a repeating XOR key: estimate its size, then solve each byte column."""
    if len(data) < 16:
        raise AnalysisError("Need at least 16 ciphertext bytes to break repeating-key XOR.")
    if key_size is not None:
        if not 1 <= key_size <= len(data):
            raise InvalidKeyError("key_size must be between 1 and the ciphertext length.")
        sizes = [key_size]
    else:
        sizes = [k for k, _ in estimate_xor_key_sizes(data, max_size)]
        if not sizes:
            raise AnalysisError("Ciphertext is too short to estimate a key size.")
    found: dict[bytes, XorCandidate] = {}
    for k in sizes:
        key = bytes(_xor_byte_ranking(data[i::k])[0][1] for i in range(k))
        key = reduce_repeating_key(key)
        plain = bytes(b ^ key[i % len(key)] for i, b in enumerate(data))
        found[key] = XorCandidate(key, plain.decode("utf-8", errors="replace"),
                                  score_english_bytes(plain))
    ranked = sorted(found.values(), key=lambda c: -c.score)
    for position, cand in enumerate(ranked, 1):
        cand.rank = position
    return ranked[:top]


# ----------------------------------------------------------------------------
# 7.4 Text analyser and attack dispatcher
# ----------------------------------------------------------------------------

@dataclass
class AnalysisReport:
    alphabet: str
    total_chars: int
    letters: int
    ioc: float
    expected_ioc: float
    random_ioc: float
    chi2: float
    entropy: float
    frequencies: list[tuple[str, int, float]] = field(default_factory=list)
    diagnosis: str = ""
    suggestions: list[str] = field(default_factory=list)


def analyze_text(text: str, alphabet: Alphabet = ENGLISH,
                 profile: FrequencyProfile | None = None) -> AnalysisReport:
    """Compute statistics and a rule-of-thumb diagnosis of what kind of text this is."""
    profile = profile or FrequencyProfile.for_alphabet(alphabet)
    counts = letter_counts(text, alphabet)
    n = sum(counts)
    if n == 0:
        raise AnalysisError(f"No letters of the '{alphabet.name}' alphabet found in the text.")
    ioc, chi2 = index_of_coincidence(counts), chi_squared(counts, profile)
    random_ioc, expected = 1 / alphabet.size, profile.expected_ioc
    rows = sorted(((alphabet.letters[i], c, 100 * c / n) for i, c in enumerate(counts)),
                  key=lambda row: (-row[1], row[0]))
    span = expected - random_ioc
    closeness = (ioc - random_ioc) / span if span > 1e-9 else 0.0   # 0 = random, 1 = language
    fit = chi2 / n
    suggestions: list[str] = []
    if n < 30:
        diagnosis = "The sample is very short; every statistic below is unreliable."
    elif closeness >= 0.85 and fit < 0.35:
        diagnosis = ("Letter distribution matches the language: plaintext, or a "
                     "transposition cipher that only rearranges letters.")
        suggestions.append("Try columnar transposition analysis (anagramming) if it looks scrambled.")
    elif closeness >= 0.85:
        diagnosis = ("IoC is language-like but the letters are permuted: a monoalphabetic "
                     "substitution such as Caesar, ROT-N or Affine.")
        suggestions.append("Run: crack caesar   or   crack affine")
    elif closeness >= 0.35:
        diagnosis = "IoC sits between language and random: a short-key polyalphabetic cipher."
        suggestions.append("Run: keylen   then   crack vigenere")
    else:
        diagnosis = ("IoC is close to random: a long-key / autokey polyalphabetic cipher, "
                     "a rotor machine, or non-text data.")
        suggestions.append("Check for XOR/hex/base64 data, or try a longer --max-key-length.")
    return AnalysisReport(alphabet.name, len(text), n, ioc, expected, random_ioc, chi2,
                          shannon_entropy(counts), rows, diagnosis, suggestions)


CRACK_METHODS = ("caesar", "affine", "vigenere", "xor")
_CRACK_ALIASES = {"rot": "caesar", "rotn": "caesar", "rot13": "caesar", "transposition": "columnar"}
_CRACK_PARAMS = {"caesar": (), "affine": (), "vigenere": ("key_length", "max_key_length"),
                 "xor": ("format", "key_size")}


def run_crack(method: str, text: str, alphabet: Alphabet, params: Mapping[str, Any] | None = None,
              top: int = 5, reference: str | None = None) -> list[dict[str, Any]]:
    """Dispatch an attack and return JSON-friendly candidate dictionaries."""
    if not text or not text.strip():
        raise InvalidInputError("No ciphertext was provided.")
    key = _canon(method)
    key = _CRACK_ALIASES.get(key, key)
    if key not in CRACK_METHODS:
        raise UnknownCipherError(
            f"Cannot crack {method!r}. Supported methods: {', '.join(CRACK_METHODS)}.")
    typed = Params(params)
    typed.reject_unknown(_CRACK_PARAMS[key], f"crack {key}")
    top = max(1, parse_int(top, "top"))
    profile = (FrequencyProfile.from_text(alphabet, reference) if reference
               else FrequencyProfile.for_alphabet(alphabet))
    if key == "caesar":
        return [c.to_dict() for c in brute_force_caesar(text, alphabet, profile, top)]
    if key == "affine":
        return [c.to_dict() for c in brute_force_affine(text, alphabet, profile, top)]
    if key == "vigenere":
        return [c.to_dict() for c in break_vigenere(
            text, alphabet, profile, key_length=typed.get_int("key_length"),
            max_key_length=typed.get_int("max_key_length", 20), top=top)]
    data = XorCipher.parse_bytes(text, typed.get_choice("format", XorCipher.FORMATS, "hex"))
    size = typed.get_int("key_size")
    found = (brute_force_xor_single_byte(data, top) if size == 1
             else break_repeating_xor(data, key_size=size, top=top))
    return [c.to_dict() for c in found]


# ============================================================================
# SECTION 8 - TEXT & FILE I/O
# ============================================================================

def configure_console() -> None:
    """Force UTF-8 on the standard streams (important for Arabic on Windows)."""
    for stream in (sys.stdin, sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if callable(reconfigure):
            with contextlib.suppress(ValueError, OSError):
                reconfigure(encoding="utf-8", errors="replace")
    if os.name == "nt":
        with contextlib.suppress(Exception):
            import ctypes
            ctypes.windll.kernel32.SetConsoleOutputCP(65001)  # type: ignore[attr-defined]
            ctypes.windll.kernel32.SetConsoleCP(65001)        # type: ignore[attr-defined]


def normalize_text(text: str) -> str:
    """NFC-normalise, unify line endings and drop a stray byte-order mark."""
    text = text.replace("\r\n", "\n").replace("\r", "\n").lstrip("\ufeff")
    return unicodedata.normalize("NFC", text)


def read_text_file(path: str | Path) -> str:
    """Read a text file as UTF-8 (BOM-tolerant), UTF-16 or Windows-1256 (Arabic)."""
    p = Path(path).expanduser()
    if not p.is_file():
        raise FileAccessError(f"Input file not found: {p}")
    try:
        raw = p.read_bytes()
    except OSError as exc:
        raise FileAccessError(f"Cannot read {p}: {exc.strerror or exc}") from None
    if not raw.strip():
        raise InvalidInputError(f"Input file is empty: {p}")
    encodings = (["utf-16"] if raw.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)) else []
                 ) + ["utf-8-sig", "cp1256"]
    for encoding in encodings:
        try:
            return normalize_text(raw.decode(encoding))
        except UnicodeDecodeError:
            continue
    raise FileAccessError(f"Cannot decode {p}: save it as UTF-8 text.")


def write_text_file(path: str | Path, text: str) -> Path:
    """Write UTF-8 text, creating parent folders as needed."""
    p = Path(path).expanduser()
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8", newline="")
    except OSError as exc:
        raise FileAccessError(f"Cannot write {p}: {exc.strerror or exc}") from None
    return p


def resolve_text(text: str | None, file: str | None, allow_stdin: bool = True) -> str:
    """Pick input from --text, --file or piped stdin; reject empty input."""
    if text is not None and file:
        raise InvalidInputError("Use either --text or --file, not both.")
    if file:
        return read_text_file(file)
    if text is not None:
        if not text.strip():
            raise InvalidInputError("The provided text is empty.")
        return normalize_text(text)
    if allow_stdin and not sys.stdin.isatty():
        piped = normalize_text(sys.stdin.read())
        if piped.strip():
            return piped
    raise InvalidInputError("No input given: use --text, --file, or pipe text into the program.")


def parse_kv_pairs(pairs: Iterable[str]) -> dict[str, str]:
    """Turn ``['key=value', ...]`` (from repeated --param) into a dict."""
    result: dict[str, str] = {}
    for item in pairs:
        name, sep, value = item.partition("=")
        if not sep or not name.strip():
            raise InvalidInputError(f"Invalid --param {item!r}: expected KEY=VALUE.")
        result[name.strip()] = value
    return result


# ============================================================================
# SECTION 9 - BATCH PROCESSING & FACADE
# ============================================================================

def run_cipher(action: str, cipher_name: str, text: str, params: Mapping[str, Any] | None = None,
               alphabet: Alphabet | str | None = None, fold: bool = True) -> str:
    """Encrypt or decrypt ``text`` - the one function the CLI, menu and batch all use."""
    action = str(action).strip().lower()
    if action not in ("encrypt", "decrypt"):
        raise InvalidInputError(f"Action must be 'encrypt' or 'decrypt' (got {action!r}).")
    if text is None or not str(text).strip():
        raise InvalidInputError("No input text was provided.")
    cipher = build_cipher(cipher_name, params, alphabet, fold)
    return cipher.encrypt(text) if action == "encrypt" else cipher.decrypt(text)


@dataclass
class JobResult:
    index: int
    job_id: str
    action: str
    ok: bool
    output: Any = None
    error: str | None = None
    output_file: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {k: v for k, v in asdict(self).items() if v is not None}


class BatchProcessor:
    """Runs a list of JSON job dictionaries and collects per-job results.

    Job fields: ``id``, ``action`` (encrypt | decrypt | crack | keylen | analyze),
    ``cipher`` / ``method``, ``params``, ``alphabet``, ``fold``, ``text`` or
    ``input_file``, ``output_file``, ``top``, ``reference_file``.
    """

    ACTIONS = ("encrypt", "decrypt", "crack", "keylen", "analyze")

    def __init__(self, base_dir: str | Path | None = None, fail_fast: bool = False) -> None:
        self.base_dir = Path(base_dir) if base_dir else Path.cwd()
        self.fail_fast = fail_fast

    @staticmethod
    def load_jobs(path: str | Path) -> tuple[list[dict[str, Any]], Path]:
        """Parse a batch file; supports ``{"defaults": {...}, "jobs": [...]}`` or a bare list."""
        p = Path(path).expanduser()
        raw = read_text_file(p)
        try:
            document = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise BatchError(f"{p}: invalid JSON ({exc.msg}, line {exc.lineno}, "
                             f"column {exc.colno}).") from None
        defaults: Any = {}
        jobs: Any = document
        if isinstance(document, dict):
            defaults = document.get("defaults") or {}
            jobs = document.get("jobs")
        if not isinstance(defaults, dict):
            raise BatchError("'defaults' must be a JSON object.")
        if not isinstance(jobs, list) or not jobs:
            raise BatchError("The batch file must contain a non-empty list of jobs.")
        merged: list[dict[str, Any]] = []
        for number, job in enumerate(jobs, 1):
            if not isinstance(job, dict):
                raise BatchError(f"Job #{number} must be a JSON object.")
            entry = {**defaults, **job}
            if isinstance(defaults.get("params"), dict) and isinstance(job.get("params"), dict):
                entry["params"] = {**defaults["params"], **job["params"]}
            merged.append(entry)
        return merged, p.parent

    def _path(self, name: str) -> Path:
        p = Path(str(name)).expanduser()
        return p if p.is_absolute() else self.base_dir / p

    def _job_text(self, job: Mapping[str, Any]) -> str:
        has_text = job.get("text") not in (None, "")
        if has_text and job.get("input_file"):
            raise BatchError("Give either 'text' or 'input_file', not both.")
        if job.get("input_file"):
            return read_text_file(self._path(job["input_file"]))
        if has_text:
            return normalize_text(str(job["text"]))
        raise InvalidInputError("Job has neither 'text' nor 'input_file'.")

    def run(self, jobs: Sequence[Mapping[str, Any]]) -> list[JobResult]:
        results: list[JobResult] = []
        for number, job in enumerate(jobs, 1):
            result = self._run_job(number, job)
            results.append(result)
            if self.fail_fast and not result.ok:
                break
        return results

    def _run_job(self, number: int, job: Mapping[str, Any]) -> JobResult:
        job_id = str(job.get("id", f"job-{number}"))
        action = str(job.get("action", "")).strip().lower()
        try:
            if action not in self.ACTIONS:
                raise BatchError(f"Unknown action {job.get('action')!r}; use one of "
                                 f"{', '.join(self.ACTIONS)}.")
            text = self._job_text(job)
            fold = Params({"fold": job.get("fold")}).get_bool("fold", True)
            alphabet = get_alphabet(job.get("alphabet"), fold=fold)
            params = job.get("params") or {}
            if not isinstance(params, dict):
                raise BatchError("'params' must be a JSON object.")
            output: Any
            if action in ("encrypt", "decrypt"):
                if not job.get("cipher"):
                    raise BatchError("Missing 'cipher' for encrypt/decrypt job.")
                output = run_cipher(action, str(job["cipher"]), text, params, alphabet, fold)
            elif action == "crack":
                method = job.get("method") or job.get("cipher")
                if not method:
                    raise BatchError("Missing 'method' for crack job.")
                reference = (read_text_file(self._path(job["reference_file"]))
                             if job.get("reference_file") else None)
                output = run_crack(str(method), text, alphabet, params,
                                   top=job.get("top", 5), reference=reference)
            elif action == "keylen":
                output = [e.to_dict() for e in estimate_key_length(
                    text, alphabet, max_len=parse_int(params.get("max_key_length", 20),
                                                      "max_key_length"))][:parse_int(job.get("top", 5), "top")]
            else:
                output = asdict(analyze_text(text, alphabet))
            saved = None
            if job.get("output_file"):
                body = output if isinstance(output, str) else json.dumps(output, ensure_ascii=False, indent=2)
                saved = str(write_text_file(self._path(job["output_file"]), body))
            return JobResult(number, job_id, action, True, output, output_file=saved)
        except (CipherSuiteError, OSError) as exc:
            return JobResult(number, job_id, action or "?", False, error=str(exc))
        except (TypeError, ValueError, KeyError) as exc:
            return JobResult(number, job_id, action or "?", False, error=f"Malformed job: {exc!r}")


def export_results(results: Sequence[JobResult], path: str | Path | None = None) -> str:
    """Serialise batch results as pretty JSON; optionally write them to ``path``."""
    payload = json.dumps({"results": [r.to_dict() for r in results],
                          "succeeded": sum(r.ok for r in results),
                          "failed": sum(not r.ok for r in results)},
                         ensure_ascii=False, indent=2)
    if path:
        write_text_file(path, payload)
    return payload


# ============================================================================
# SECTION 10 - PRESENTATION HELPERS
# ============================================================================

def format_cipher_list() -> str:
    lines = ["Available ciphers", "-----------------"]
    for cls in unique_ciphers():
        aliases = sorted(k for k, v in CIPHER_REGISTRY.items() if v is cls and k != _canon(cls.name))
        lines.append(f"{cls.name:<10} {cls.summary}")
        for spec in cls.PARAMS:
            if spec.required:
                note = "required"
            elif spec.default not in (None, ""):
                note = f"default: {spec.default}"
            else:
                note = "optional"
            lines.append(f"    --{spec.name.replace('_', '-'):<14} {spec.help} ({note})")
        if aliases:
            lines.append(f"    aliases: {', '.join(aliases)}")
    lines += ["", "Attack methods (crack): " + ", ".join(CRACK_METHODS),
              "Other tools: keylen (Kasiski/IoC), analyze (statistics + diagnosis)"]
    return "\n".join(lines)


def format_candidates(rows: Sequence[Mapping[str, Any]], preview_width: int = 60) -> str:
    if not rows:
        return "(no candidates)"
    lines = []
    for row in rows:
        if "chi2" in row:
            chi = "n/a" if row["chi2"] is None else f"{row['chi2']:.1f}"
            metric = f"chi2={chi} IoC={row['ioc']:.4f}"
        else:
            metric = f"score={row['score']:.2f}"
        preview = " ".join(str(row["plaintext"]).split())
        if len(preview) > preview_width:
            preview = preview[:preview_width - 3] + "..."
        lines.append(f"#{row['rank']:<2} key={row['key']:<16} {metric:<26} {preview}")
    return "\n".join(lines)


def format_key_lengths(rows: Sequence[Mapping[str, Any]]) -> str:
    lines = ["rank  length  avg IoC   Kasiski votes"]
    for row in rows:
        marker = "   <- most plausible" if row["rank"] == 1 else ""
        lines.append(f"{row['rank']:<5} {row['length']:<7} {row['avg_ioc']:<9.4f} "
                     f"{row['kasiski_votes']:<5}{marker}")
    return "\n".join(lines)


def format_analysis(report: AnalysisReport, top: int = 10) -> str:
    lines = [
        f"Alphabet             : {report.alphabet}",
        f"Characters / letters : {report.total_chars} / {report.letters}",
        f"Index of coincidence : {report.ioc:.4f}  (language ~ {report.expected_ioc:.4f}, "
        f"random ~ {report.random_ioc:.4f})",
        f"Chi-squared vs profile: {report.chi2:.1f}  ({report.chi2 / report.letters:.3f} per letter)",
        f"Entropy              : {report.entropy:.3f} bits/letter",
        "", "Most frequent letters:",
    ]
    for letter, count, percent in report.frequencies[:top]:
        lines.append(f"  {letter}  {count:>5}  {percent:5.2f}%  {'#' * round(percent)}")
    lines += ["", f"Diagnosis: {report.diagnosis}"]
    lines += [f"Suggestion: {s}" for s in report.suggestions]
    return "\n".join(lines)


# ============================================================================
# SECTION 11 - COMMAND LINE INTERFACE & INTERACTIVE MENU
# ============================================================================

def emit(text: str, output: str | None) -> None:
    """Print ``text`` or save it (exactly, without adding a newline) to ``output``."""
    if output:
        path = write_text_file(output, text)
        print(f"Saved {len(text)} characters to {path}")
    else:
        print(text)


def _cipher_flag_table() -> dict[str, tuple[str, list[str]]]:
    """Union of all cipher parameters -> (help text, ciphers that use it)."""
    table: dict[str, tuple[str, list[str]]] = {}
    for cls in unique_ciphers():
        for spec in cls.PARAMS:
            help_text, users = table.setdefault(spec.name, (spec.help, []))
            users.append(cls.name)
    return table


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="cipher_suite", allow_abbrev=False,
        description="Cipher Machine & Cryptanalysis Suite - classical ciphers and attacks.",
        epilog="Run with no arguments for the interactive menu.  Educational use only.")
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    parser.add_argument("--debug", action="store_true", help="show tracebacks for unexpected errors")
    sub = parser.add_subparsers(dest="command", metavar="COMMAND")

    io_opts = argparse.ArgumentParser(add_help=False)
    io_opts.add_argument("-t", "--text", help="input text (or pipe text via stdin)")
    io_opts.add_argument("-f", "--file", help="read input from a UTF-8 text file")
    io_opts.add_argument("-o", "--output", help="write the result to this file")
    io_opts.add_argument("--alphabet", default="english",
                         help="english | arabic | custom:<letters> (default: english)")
    io_opts.add_argument("--no-fold", action="store_true",
                         help="do not fold Arabic letter variants (alef forms, ta marbuta, ...)")

    for command, verb in (("encrypt", "Encrypt"), ("decrypt", "Decrypt")):
        p = sub.add_parser(command, parents=[io_opts], allow_abbrev=False, help=f"{verb} text")
        p.add_argument("cipher", metavar="CIPHER", help="cipher name (see 'list')")
        p.add_argument("-p", "--param", action="append", default=[], metavar="KEY=VALUE",
                       help="extra cipher parameter (repeatable)")
        for name, (help_text, users) in sorted(_cipher_flag_table().items()):
            p.add_argument("--" + name.replace("_", "-"), dest=f"p_{name}", default=None,
                           help=f"{help_text} [{', '.join(users)}]")

    crack = sub.add_parser("crack", parents=[io_opts], allow_abbrev=False,
                           help="break a cipher (brute force / statistics)")
    crack.add_argument("method", choices=sorted(set(CRACK_METHODS) | set(_CRACK_ALIASES) - {"transposition"}),
                       metavar="METHOD", help="caesar | affine | vigenere | xor")
    crack.add_argument("--top", type=int, default=5, help="number of candidates to show")
    crack.add_argument("--key-length", type=int, help="known key length (vigenere) ")
    crack.add_argument("--max-key-length", type=int, default=20, help="largest key length to test")
    crack.add_argument("--key-size", type=int, help="known key size in bytes (xor; 1 = single byte)")
    crack.add_argument("--format", choices=XorCipher.FORMATS, default="hex",
                       help="ciphertext representation for xor")
    crack.add_argument("--reference", help="text file used to build the frequency profile")
    crack.add_argument("--json", action="store_true", help="machine-readable output")

    keylen = sub.add_parser("keylen", parents=[io_opts], allow_abbrev=False,
                            help="estimate a polyalphabetic key length (Kasiski + IoC)")
    keylen.add_argument("--max-key-length", type=int, default=20)
    keylen.add_argument("--top", type=int, default=6)
    keylen.add_argument("--json", action="store_true")

    analyze = sub.add_parser("analyze", parents=[io_opts], allow_abbrev=False,
                             help="letter statistics and a cipher-type diagnosis")
    analyze.add_argument("--reference", help="text file used to build the frequency profile")
    analyze.add_argument("--json", action="store_true")

    batch = sub.add_parser("batch", allow_abbrev=False, help="run jobs from a JSON file")
    batch.add_argument("jobs_file", help="JSON file with a list of jobs")
    batch.add_argument("-o", "--output", help="write the JSON results to this file")
    batch.add_argument("--fail-fast", action="store_true", help="stop at the first failing job")

    sub.add_parser("list", help="list ciphers, parameters and attack methods")
    sub.add_parser("demo", help="run a short guided demonstration")
    tests = sub.add_parser("test", help="run the built-in unit tests")
    tests.add_argument("-v", "--verbose", action="store_true")
    return parser


def _cipher_params(args: argparse.Namespace) -> dict[str, Any]:
    params: dict[str, Any] = {}
    for name in _cipher_flag_table():
        value = getattr(args, f"p_{name}", None)
        if value is not None:
            params[name] = value
    params.update(parse_kv_pairs(args.param))
    return params


def _profile_note(alphabet: Alphabet, reference: str | None) -> None:
    if reference is None and FrequencyProfile.for_alphabet(alphabet).is_uniform:
        print(f"Note: no built-in frequency profile for '{alphabet.name}'; results are weak. "
              "Supply --reference <text file> for a meaningful ranking.", file=sys.stderr)


def cmd_crypt(args: argparse.Namespace) -> int:
    text = resolve_text(args.text, args.file)
    result = run_cipher(args.command, args.cipher, text, _cipher_params(args),
                        args.alphabet, not args.no_fold)
    emit(result, args.output)
    return 0


def cmd_crack(args: argparse.Namespace) -> int:
    alphabet = get_alphabet(args.alphabet, fold=not args.no_fold)
    text = resolve_text(args.text, args.file)
    reference = read_text_file(args.reference) if args.reference else None
    _profile_note(alphabet, reference)
    params = {"key_length": args.key_length, "max_key_length": args.max_key_length,
              "key_size": args.key_size, "format": args.format}
    method = _CRACK_ALIASES.get(_canon(args.method), _canon(args.method))
    params = {k: v for k, v in params.items() if k in _CRACK_PARAMS[method] and v is not None}
    rows = run_crack(args.method, text, alphabet, params, top=args.top, reference=reference)
    emit(json.dumps(rows, ensure_ascii=False, indent=2) if args.json else format_candidates(rows),
         args.output)
    return 0


def cmd_keylen(args: argparse.Namespace) -> int:
    alphabet = get_alphabet(args.alphabet, fold=not args.no_fold)
    text = resolve_text(args.text, args.file)
    rows = [e.to_dict() for e in estimate_key_length(text, alphabet, max_len=args.max_key_length)]
    rows = rows[:max(1, args.top)]
    emit(json.dumps(rows, indent=2) if args.json else format_key_lengths(rows), args.output)
    return 0


def cmd_analyze(args: argparse.Namespace) -> int:
    alphabet = get_alphabet(args.alphabet, fold=not args.no_fold)
    text = resolve_text(args.text, args.file)
    reference = read_text_file(args.reference) if args.reference else None
    profile = FrequencyProfile.from_text(alphabet, reference) if reference else None
    report = analyze_text(text, alphabet, profile)
    emit(json.dumps(asdict(report), ensure_ascii=False, indent=2) if args.json
         else format_analysis(report), args.output)
    return 0


def cmd_batch(args: argparse.Namespace) -> int:
    jobs, base = BatchProcessor.load_jobs(args.jobs_file)
    results = BatchProcessor(base, fail_fast=args.fail_fast).run(jobs)
    payload = export_results(results, args.output)
    if args.output:
        failed = sum(not r.ok for r in results)
        print(f"Processed {len(results)} job(s), {failed} failed. Results saved to {args.output}")
    else:
        print(payload)
    return 1 if any(not r.ok for r in results) else 0


def run_self_tests(verbosity: int = 1) -> bool:
    """Run every TestCase in this module and report success."""
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=verbosity, stream=sys.stdout).run(suite)
    return result.wasSuccessful()


class InteractiveMenu:
    """Prompt-driven front end; ``read``/``write`` are injectable so it can be tested."""

    def __init__(self, read: Callable[[str], str] = input,
                 write: Callable[[str], None] = print) -> None:
        self._read = read
        self._write = write

    # -- prompt helpers ------------------------------------------------------
    def _ask(self, label: str, default: str | None = None) -> str:
        suffix = f" [{default}]" if default not in (None, "") else ""
        answer = self._read(f"{label}{suffix}: ").strip()
        return answer if answer else (default or "")

    def _pick(self, title: str, options: Sequence[str]) -> int:
        self._write(f"\n{title}")
        for number, option in enumerate(options, 1):
            self._write(f"  {number}) {option}")
        while True:
            answer = self._ask("Choose a number")
            if answer.isdigit() and 1 <= int(answer) <= len(options):
                return int(answer) - 1
            self._write(f"Please enter a number between 1 and {len(options)}.")

    def _ask_alphabet(self) -> Alphabet:
        choice = self._pick("Alphabet", ["English", "Arabic", "Custom letters"])
        if choice == 0:
            return ENGLISH
        if choice == 1:
            return ARABIC
        return Alphabet.custom(self._ask("Letters in order (e.g. abcdefghijklmnopqrstuvwxyz0123456789)"))

    def _ask_text(self) -> str:
        if self._pick("Input source", ["Type text", "Read from a file"]) == 1:
            return read_text_file(self._ask("File path"))
        while True:
            text = self._ask("Text")
            if text.strip():
                return normalize_text(text)
            self._write("Text must not be empty.")

    def _maybe_save(self, text: str) -> None:
        target = self._ask("Save result to file (blank = no)")
        if target:
            self._write(f"Saved to {write_text_file(target, text)}")

    # -- menu actions --------------------------------------------------------
    def _crypt(self, action: str) -> None:
        classes = unique_ciphers()
        cls = classes[self._pick(f"Cipher to {action} with", [c.name for c in classes])]
        alphabet = self._ask_alphabet() if cls.uses_alphabet else ENGLISH
        params: dict[str, Any] = {}
        for spec in cls.PARAMS:
            default = None if spec.required or spec.default in (None, "") else str(spec.default)
            while True:
                value = self._ask(f"{spec.name} - {spec.help}", default)
                if value or not spec.required:
                    break
                self._write(f"'{spec.name}' is required.")
            if value:
                params[spec.name] = value
        text = self._ask_text()
        result = run_cipher(action, cls.name, text, params, alphabet)
        self._write(f"\nResult:\n{result}")
        self._maybe_save(result)

    def _crack(self) -> None:
        method = CRACK_METHODS[self._pick("Attack method", list(CRACK_METHODS))]
        alphabet = self._ask_alphabet() if method != "xor" else ENGLISH
        params: dict[str, Any] = {}
        if method == "vigenere":
            params["key_length"] = self._ask("Known key length (blank = estimate)")
        if method == "xor":
            params["format"] = self._ask("Ciphertext format (hex/base64/utf8)", "hex")
        text = self._ask_text()
        rows = run_crack(method, text, alphabet, params, top=5)
        self._write("\n" + format_candidates(rows))

    def _keylen(self) -> None:
        alphabet = self._ask_alphabet()
        text = self._ask_text()
        rows = [e.to_dict() for e in estimate_key_length(text, alphabet)][:6]
        self._write("\n" + format_key_lengths(rows))

    def _analyze(self) -> None:
        alphabet = self._ask_alphabet()
        self._write("\n" + format_analysis(analyze_text(self._ask_text(), alphabet)))

    def _batch(self) -> None:
        jobs, base = BatchProcessor.load_jobs(self._ask("Path to JSON job file"))
        results = BatchProcessor(base).run(jobs)
        out = self._ask("Save results to (blank = print)")
        payload = export_results(results, out or None)
        self._write(f"Saved to {out}" if out else payload)

    def run(self) -> int:
        self._write(f"\n=== Cipher Machine & Cryptanalysis Suite v{__version__} ===")
        entries: list[tuple[str, Callable[[], None]]] = [
            ("Encrypt text", lambda: self._crypt("encrypt")),
            ("Decrypt text", lambda: self._crypt("decrypt")),
            ("Crack a cipher", self._crack),
            ("Estimate key length (Kasiski / IoC)", self._keylen),
            ("Analyze text statistics", self._analyze),
            ("Run a JSON batch file", self._batch),
            ("Show ciphers and parameters", lambda: self._write(format_cipher_list())),
            ("Run built-in unit tests", lambda: run_self_tests(1)),
        ]
        while True:
            self._write("\nMain menu")
            for number, (label, _) in enumerate(entries, 1):
                self._write(f"  {number}) {label}")
            self._write("  0) Exit")
            try:
                choice = self._ask("Select").lower()
            except (EOFError, KeyboardInterrupt):
                self._write("\nGoodbye.")
                return 0
            if choice in ("0", "q", "quit", "exit"):
                self._write("Goodbye.")
                return 0
            if not (choice.isdigit() and 1 <= int(choice) <= len(entries)):
                self._write("Invalid choice.")
                continue
            try:
                entries[int(choice) - 1][1]()
            except CipherSuiteError as exc:
                self._write(f"Error: {exc}")
            except EOFError:
                self._write("\nInput closed. Goodbye.")
                return 0
            except KeyboardInterrupt:
                self._write("\nCancelled.")


def main(argv: Sequence[str] | None = None) -> int:
    """Program entry point; returns a process exit code."""
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command is None:
            if sys.stdin.isatty():
                return InteractiveMenu().run()
            parser.print_help()
            return 0
        if args.command in ("encrypt", "decrypt"):
            return cmd_crypt(args)
        handlers = {"crack": cmd_crack, "keylen": cmd_keylen, "analyze": cmd_analyze,
                    "batch": cmd_batch}
        if args.command in handlers:
            return handlers[args.command](args)
        if args.command == "list":
            print(format_cipher_list())
            return 0
        if args.command == "demo":
            print(run_demo())
            return 0
        if args.command == "test":
            return 0 if run_self_tests(2 if args.verbose else 1) else 1
        parser.error(f"Unhandled command {args.command!r}")
    except CipherSuiteError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("\nInterrupted.", file=sys.stderr)
        return 130
    except Exception as exc:  # pragma: no cover - last-resort safety net
        if getattr(args, "debug", False):
            raise
        print(f"Unexpected error: {exc!r} (re-run with --debug for a traceback)", file=sys.stderr)
        return 3
    return 0


# ============================================================================
# SECTION 12 - SAMPLE CORPORA, DEMO & UNIT TESTS
# ============================================================================

SAMPLE_ENGLISH = (
    "Cryptography is the practice of protecting information by transforming it into a form "
    "that unintended readers cannot understand. Long before computers existed, military "
    "commanders and diplomats relied on simple substitutions and transpositions to keep their "
    "messages secret. Analysts soon discovered that every language leaves statistical "
    "fingerprints, and that counting letters can reveal the hidden structure of an apparently "
    "random message. Modern algorithms are far stronger, yet the lessons of the classical era "
    "remain valuable because they teach how patterns leak and why careful key management "
    "matters more than clever tricks. The Vigenere cipher was once called unbreakable because "
    "it flattens the letter frequencies that betray a simple substitution. Friedrich Kasiski "
    "and later William Friedman showed that repeated fragments and the index of coincidence "
    "expose the length of the key. Once the length is known, the message splits into several "
    "Caesar ciphers, and each of them falls quickly to frequency analysis. This is why the "
    "weakness of periodic keys is always the first topic in any course on classical "
    "cryptanalysis."
)

SAMPLE_ARABIC = (
    "اللغة العربية من أقدم اللغات الحية في العالم، ويتحدث بها مئات الملايين من البشر في الوطن "
    "العربي وخارجه. وتتميز بثراء مفرداتها وجمال خطها وعمق بلاغتها. وقد ساهم العلماء العرب عبر "
    "القرون في نقل المعرفة بين الحضارات، فبرعوا في الطب والفلك والرياضيات والفلسفة، وكان علم "
    "التعمية وكشف المعمى من العلوم التي ازدهرت في بغداد، إذ وضع الكندي رسالة في استخراج المعمى "
    "بتحليل تكرار الحروف، وهي من أقدم ما كتب في تحليل الشيفرات."
)


def run_demo() -> str:
    """Encrypt a message with every cipher and crack two of them; returns a report."""
    plain = "Meet me at the old library at midnight."
    tour = [("caesar", {"shift": 3}), ("rot", {}), ("affine", {"a": 5, "b": 8}),
            ("vigenere", {"key": "LEMON"}), ("vigenere", {"key": "QUEENLY", "mode": "autokey"}),
            ("playfair", {"key": "PLAYFAIR EXAMPLE", "group_size": 5}),
            ("columnar", {"key": "ZEBRAS", "padding": "pad", "pad_char": "Q"}),
            ("xor", {"key": "k3y", "format": "base64"}),
            ("enigma", {"positions": "Q E V", "plugboard": "AB CD EF"})]
    lines = [f"Plaintext: {plain}", ""]
    for name, params in tour:
        cipher = build_cipher(name, params)
        encrypted = cipher.encrypt(plain)
        label = name + ("/autokey" if params.get("mode") == "autokey" else "")
        lines += [f"{label:<16} {encrypted}", f"{'':<16} -> decrypts to: {cipher.decrypt(encrypted)}"]
    caesar_text = CaesarCipher(11).encrypt(SAMPLE_ENGLISH)
    lines += ["", "Brute-forcing a Caesar-encrypted paragraph (true shift 11):",
              format_candidates([c.to_dict() for c in brute_force_caesar(caesar_text, top=3)], 48)]
    vig_text = VigenereCipher("CIPHER").encrypt(SAMPLE_ENGLISH)
    lines += ["", "Breaking a Vigenere-encrypted paragraph (true key CIPHER):",
              format_key_lengths([e.to_dict() for e in estimate_key_length(vig_text)][:4]),
              format_candidates([c.to_dict() for c in break_vigenere(vig_text, top=2)], 48)]
    return "\n".join(lines)


def _run_cli(*argv: str) -> tuple[int, str, str]:
    """Invoke main() capturing stdout/stderr (used by the tests)."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main(list(argv))
    return code, out.getvalue(), err.getvalue()


class TestAlphabet(unittest.TestCase):
    def test_sizes_and_letters(self):
        self.assertEqual(ENGLISH.size, 26)
        self.assertEqual(ARABIC.size, 28)
        self.assertTrue(all("\u0621" <= c <= "\u064a" for c in ARABIC.letters))

    def test_invalid_alphabets(self):
        with self.assertRaises(AlphabetError):
            Alphabet("AAB")
        with self.assertRaises(AlphabetError):
            Alphabet("A")

    def test_locate_and_render_preserve_case(self):
        self.assertEqual(ENGLISH.locate("c"), (2, True))
        self.assertEqual(ENGLISH.locate("C"), (2, False))
        self.assertIsNone(ENGLISH.locate("3"))
        self.assertEqual(ENGLISH.render(2, True), "c")

    def test_arabic_fold(self):
        for variant in "أإآ":
            self.assertEqual(ARABIC.locate(variant), (0, False))
        self.assertIsNone(ARABIC.without_fold().locate("أ"))

    def test_custom_alphabet_is_case_insensitive(self):
        alpha = get_alphabet("custom:abc012")
        self.assertEqual(alpha.letters, "ABC012")
        self.assertEqual(alpha.locate("b"), (1, True))

    def test_get_alphabet(self):
        self.assertIs(get_alphabet(None), ENGLISH)
        self.assertEqual(get_alphabet("AR").name, "arabic")
        with self.assertRaises(AlphabetError):
            get_alphabet("klingon")


class TestNumberTheoryAndParams(unittest.TestCase):
    def test_inverse(self):
        self.assertEqual(mod_inverse(5, 26), 21)
        self.assertEqual((3 * mod_inverse(3, 28)) % 28, 1)
        with self.assertRaises(InvalidKeyError):
            mod_inverse(2, 26)

    def test_egcd_and_coprimes(self):
        g, x, y = egcd(240, 46)
        self.assertEqual((g, 240 * x + 46 * y), (2, 2))
        self.assertEqual(len(coprime_values(26)), 12)

    def test_parse_int(self):
        self.assertEqual(parse_int(" -7 "), -7)
        self.assertEqual(parse_int(4.0), 4)
        for bad in ("", "abc", "3.5", None, True, 2.5):
            with self.assertRaises(InvalidKeyError):
                parse_int(bad, "x")

    def test_params_helpers(self):
        p = Params({"shift-amount": "4", "flag": "yes", "mode": "AUTOKEY"})
        self.assertEqual(p.get_int("shift_amount"), 4)
        self.assertTrue(p.get_bool("flag"))
        self.assertEqual(p.get_choice("mode", ("repeat", "autokey"), "repeat"), "autokey")
        with self.assertRaises(InvalidKeyError):
            Params({"mode": "x"}).get_choice("mode", ("a", "b"), "a")
        with self.assertRaises(InvalidKeyError):
            Params({}).get_str("key", required=True)
        with self.assertRaises(InvalidKeyError):
            p.reject_unknown(["flag"], "test")


class TestCaesarAndRot(unittest.TestCase):
    def test_known_vector_and_case(self):
        self.assertEqual(CaesarCipher(3).encrypt("Hello, World!"), "Khoor, Zruog!")
        self.assertEqual(CaesarCipher(3).decrypt("Khoor, Zruog!"), "Hello, World!")

    def test_round_trip_all_shifts_including_negative_and_large(self):
        for shift in (-30, -1, 0, 1, 25, 26, 1000):
            c = CaesarCipher(shift)
            self.assertEqual(c.decrypt(c.encrypt(SAMPLE_ENGLISH)), SAMPLE_ENGLISH)

    def test_arabic(self):
        c = CaesarCipher(1, ARABIC)
        self.assertEqual(c.encrypt("ابت"), "بتث")
        self.assertEqual(c.decrypt(c.encrypt(SAMPLE_ARABIC)), ARABIC.transform(SAMPLE_ARABIC, lambda i: i))

    def test_custom_alphabet_with_digits(self):
        alpha = get_alphabet("custom:abcdefghijklmnopqrstuvwxyz0123456789")
        c = CaesarCipher(5, alpha)
        self.assertEqual(c.encrypt("a1 Ab!"), "f6 Fg!")
        self.assertEqual(c.decrypt("f6 Fg!"), "a1 Ab!")
        # digits carry no case, so a letter reached from a digit is rendered upper-case
        self.assertEqual(c.encrypt("z9"), "4E")

    def test_rot13(self):
        rot = RotNCipher(alphabet=ENGLISH)
        self.assertEqual(rot.encrypt("Hello"), "Uryyb")
        self.assertTrue(rot.is_self_inverse)
        self.assertEqual(rot.encrypt(rot.encrypt(SAMPLE_ENGLISH)), SAMPLE_ENGLISH)
        self.assertEqual(RotNCipher(alphabet=ARABIC).shift, 14)
        self.assertFalse(RotNCipher(5).is_self_inverse)


class TestAffine(unittest.TestCase):
    def test_known_vector(self):
        c = AffineCipher(5, 8)
        self.assertEqual(c.encrypt("AFFINE CIPHER"), "IHHWVC SWFRCP")
        self.assertEqual(c.decrypt("IHHWVC SWFRCP"), "AFFINE CIPHER")

    def test_invalid_multiplier_has_helpful_message(self):
        with self.assertRaises(InvalidKeyError) as ctx:
            AffineCipher(2, 3)
        self.assertIn("gcd(2, 26)", str(ctx.exception))
        with self.assertRaises(InvalidKeyError):
            AffineCipher(26, 0)

    def test_every_valid_key_round_trips(self):
        text = "The Quick Brown Fox, 123!"
        for a in coprime_values(26):
            for b in range(26):
                c = AffineCipher(a, b)
                self.assertEqual(c.decrypt(c.encrypt(text)), text)

    def test_arabic_round_trip(self):
        c = AffineCipher(3, 7, ARABIC)
        self.assertEqual(c.decrypt(c.encrypt("مرحبا بالعالم")), "مرحبا بالعالم")
        with self.assertRaises(InvalidKeyError):
            AffineCipher(4, 0, ARABIC)


class TestVigenere(unittest.TestCase):
    def test_classic_vectors(self):
        self.assertEqual(VigenereCipher("LEMON").encrypt("ATTACKATDAWN"), "LXFOPVEFRNHR")
        self.assertEqual(VigenereCipher("QUEENLY", "autokey").encrypt("ATTACKATDAWN"), "QNXEPVYTWTWP")

    def test_round_trip_preserves_case_and_punctuation(self):
        text = "Attack at Dawn, 5 o'clock!"
        for mode in VigenereCipher.MODES:
            c = VigenereCipher("Lemon", mode)
            self.assertEqual(c.decrypt(c.encrypt(text)), text)

    def test_key_ignores_non_letters_but_rejects_empty(self):
        self.assertEqual(VigenereCipher("le-mon 42").key, "LEMON")
        with self.assertRaises(InvalidKeyError):
            VigenereCipher("1234")
        with self.assertRaises(InvalidKeyError):
            VigenereCipher("KEY", "bogus")

    def test_arabic_both_modes(self):
        text = "السلام عليكم ورحمة الله"
        folded = ARABIC.transform(text, lambda i: i)   # ta marbuta -> ha (documented fold)
        for mode in VigenereCipher.MODES:
            c = VigenereCipher("مفتاح", mode, ARABIC)
            self.assertEqual(c.decrypt(c.encrypt(text)), folded)


class TestPlayfair(unittest.TestCase):
    def test_wikipedia_vector(self):
        c = PlayfairCipher("PLAYFAIR EXAMPLE")
        self.assertEqual(c.encrypt("Hide the gold in the tree stump"), "BMODZBXDNABEKUDMUIXMMOUVIF")
        self.assertEqual(c.decrypt("BMODZBXDNABEKUDMUIXMMOUVIF"), "HIDETHEGOLDINTHETREXESTUMP")

    def test_filler_stripping_and_grouping(self):
        c = PlayfairCipher("PLAYFAIR EXAMPLE", strip_filler=True, group_size=5)
        encrypted = c.encrypt("Hide the gold in the tree stump")
        self.assertEqual(encrypted.split()[0], "BMODZ")
        self.assertEqual(c.decrypt(encrypted), "HIDETHEGOLDINTHETREESTUMP")

    def test_odd_length_and_double_letters(self):
        c = PlayfairCipher("KEYWORD")
        out = c.decrypt(c.encrypt("BALLOON"))
        self.assertEqual(len(out) % 2, 0)
        self.assertEqual(out, "BALXLOON")
        with self.assertRaises(InvalidInputError):
            c.decrypt("ABC")

    def test_configurable_merge(self):
        c = PlayfairCipher("MONARCHY", merge_from="I", merge_into="J")
        self.assertNotIn("I", "".join("".join(row) for row in c.matrix))
        self.assertNotIn("I", c.decrypt(c.encrypt("INSIDE")))

    def test_invalid_configuration(self):
        for kwargs in ({"key": "123"}, {"key": "K", "merge_from": "II"},
                       {"key": "K", "merge_from": "J", "merge_into": "J"},
                       {"key": "K", "filler": "J"}):
            with self.assertRaises(InvalidKeyError):
                PlayfairCipher(**kwargs)


class TestColumnar(unittest.TestCase):
    def test_zebras_vector(self):
        c = ColumnarTranspositionCipher("ZEBRAS")
        self.assertEqual(c.encrypt("WEAREDISCOVEREDFLEEATONCE"), "EVLNACDTESEAROFODEECWIREE")
        self.assertEqual(c.decrypt("EVLNACDTESEAROFODEECWIREE"), "WEAREDISCOVEREDFLEEATONCE")

    def test_round_trip_exact_with_spaces_and_unicode(self):
        text = "Meet me at 9 - لقاء عند التاسعة!\nBring the files."
        for key in ("SECRET", "3 1 4 2 5", "كلمة"):
            c = ColumnarTranspositionCipher(key)
            self.assertEqual(c.decrypt(c.encrypt(text)), text)

    def test_padding_modes(self):
        plain = "ATTACKATDAWN"
        padded = ColumnarTranspositionCipher("KEYS", "pad", "Q")
        self.assertEqual(padded.decrypt(padded.encrypt("ATTACK")), "ATTACKQQ")
        unpadded = ColumnarTranspositionCipher("KEYS", "pad_unpad", "Q")
        self.assertEqual(unpadded.decrypt(unpadded.encrypt("ATTACK")), "ATTACK")
        self.assertEqual(unpadded.decrypt(unpadded.encrypt(plain)), plain)

    def test_invalid_keys(self):
        for key in ("A", "1 1 2", "1 3"):
            with self.assertRaises(InvalidKeyError):
                ColumnarTranspositionCipher(key)
        with self.assertRaises(InvalidKeyError):
            ColumnarTranspositionCipher("KEY", "weird")
        with self.assertRaises(InvalidKeyError):
            ColumnarTranspositionCipher("KEY", "pad", "XX")

    def test_empty_text(self):
        c = ColumnarTranspositionCipher("KEY")
        self.assertEqual(c.encrypt(""), "")
        self.assertEqual(c.decrypt(""), "")


class TestXor(unittest.TestCase):
    def test_hex_vector(self):
        self.assertEqual(XorCipher("A").encrypt("AB"), "0003")
        self.assertEqual(XorCipher("A").decrypt("0003"), "AB")

    def test_all_formats_round_trip(self):
        text = "Secret رسالة سرية"
        for fmt in ("hex", "base64"):
            for mode in XorCipher.MODES:
                c = XorCipher("key", mode=mode, output_format=fmt)
                self.assertEqual(c.decrypt(c.encrypt(text)), text)
        utf8 = XorCipher("\x01", output_format="utf8")
        self.assertEqual(utf8.decrypt(utf8.encrypt("plain ascii")), "plain ascii")

    def test_hex_key_and_stream_differs_from_repeat(self):
        repeat = XorCipher("0f0f", key_format="hex")
        stream = XorCipher("0f0f", key_format="hex", mode="stream")
        self.assertNotEqual(repeat.encrypt("hello world"), stream.encrypt("hello world"))
        self.assertEqual(len(stream.keystream(100)), 100)

    def test_errors(self):
        with self.assertRaises(InvalidKeyError):
            XorCipher("")
        with self.assertRaises(InvalidKeyError):
            XorCipher("zz", key_format="hex")
        with self.assertRaises(EncodingFormatError):
            XorCipher("a").decrypt("not hex")
        with self.assertRaises(EncodingFormatError):
            XorCipher("a").decrypt("ff")       # 0xff ^ 0x61 is not valid UTF-8
        with self.assertRaises(EncodingFormatError):
            XorCipher("a", output_format="base64").decrypt("***")
        with self.assertRaises(EncodingFormatError):
            XorCipher("\xff", output_format="utf8").encrypt("a")


class TestEnigma(unittest.TestCase):
    def test_tables_are_valid(self):
        for spec in ROTORS.values():
            self.assertTrue(_is_permutation(spec.wiring), spec.name)
        for name in REFLECTOR_TABLE:
            resolve_reflector(name)

    def test_known_vectors(self):
        e = EnigmaCipher()
        self.assertEqual(e.encrypt("AAAAA"), "BDZGO")
        self.assertEqual(e.encrypt("AAAAAAAAAA"), "BDZGOWCXLT")
        self.assertEqual(e.encrypt("HELLOWORLD"), "ILBDAAMTAZ")

    def test_reciprocal_with_plugboard_and_settings(self):
        e = EnigmaCipher(rotors="V I IV", reflector="C", rings="B U L", positions="Q E V",
                         plugboard="AB CD EF GH")
        text = "Attack at dawn, Commander!"
        encrypted = e.encrypt(text)
        self.assertNotEqual(encrypted.upper(), text.upper())
        self.assertEqual(e.decrypt(encrypted), text)
        self.assertEqual(sum(ch.isalpha() for ch in encrypted), sum(ch.isalpha() for ch in text))

    def test_no_letter_encrypts_to_itself(self):
        out = EnigmaCipher().encrypt("A" * 200 + "Q" * 200)
        self.assertTrue(all(o != i for o, i in zip(out, "A" * 200 + "Q" * 200)))

    def test_double_stepping(self):
        machine = EnigmaCipher(positions="A D U").new_machine()
        seen = []
        for _ in range(3):
            machine.press(0)
            seen.append(machine.positions)
        self.assertEqual(seen, ["ADV", "AEW", "BFX"])

    def test_settings_change_output(self):
        base = EnigmaCipher().encrypt("TESTMESSAGE")
        self.assertNotEqual(base, EnigmaCipher(rings="B A A").encrypt("TESTMESSAGE"))
        self.assertNotEqual(base, EnigmaCipher(plugboard="TE").encrypt("TESTMESSAGE"))
        self.assertNotEqual(base, EnigmaCipher(rotors="III II I").encrypt("TESTMESSAGE"))

    def test_invalid_configuration(self):
        for kwargs in ({"plugboard": "AB AC"}, {"plugboard": "AA"}, {"plugboard": "A"},
                       {"rotors": "I II"}, {"rotors": "I II XX"}, {"reflector": "Z"},
                       {"positions": "A A 27"}, {"rings": "A A !"}):
            with self.assertRaises(InvalidKeyError, msg=str(kwargs)):
                EnigmaCipher(**kwargs)

    def test_custom_rotor_accepts_wiring_and_notch(self):
        e = EnigmaCipher(rotors=f"{ROTORS['I'].wiring}:Q II III")
        self.assertEqual(e.encrypt("AAAAA"), "BDZGO")


class TestCryptanalysis(unittest.TestCase):
    def test_statistics(self):
        counts = letter_counts("AABB", ENGLISH)
        self.assertEqual(counts[:3], [2, 2, 0])
        self.assertAlmostEqual(index_of_coincidence(counts), 2 / 6)
        self.assertEqual(index_of_coincidence([1]), 0.0)
        self.assertAlmostEqual(shannon_entropy([1, 1]), 1.0)

    def test_profiles_are_normalised_and_plausible(self):
        for alphabet in (ENGLISH, ARABIC):
            profile = FrequencyProfile.for_alphabet(alphabet)
            self.assertAlmostEqual(sum(profile.probs), 1.0)
            self.assertGreater(profile.expected_ioc, 1 / alphabet.size)
        self.assertTrue(FrequencyProfile.for_alphabet(Alphabet("ABC")).is_uniform)

    def test_chi_squared_prefers_real_text(self):
        profile = FrequencyProfile.for_alphabet(ENGLISH)
        real = chi_squared(letter_counts(SAMPLE_ENGLISH, ENGLISH), profile)
        shifted = chi_squared(letter_counts(CaesarCipher(7).encrypt(SAMPLE_ENGLISH), ENGLISH), profile)
        self.assertLess(real * 5, shifted)

    def test_brute_force_caesar_english(self):
        for shift in (1, 7, 13, 25):
            cipher_text = CaesarCipher(shift).encrypt(SAMPLE_ENGLISH)
            best = brute_force_caesar(cipher_text)[0]
            self.assertEqual((best.key, best.plaintext), (shift, SAMPLE_ENGLISH))

    def test_brute_force_caesar_arabic(self):
        cipher_text = CaesarCipher(5, ARABIC).encrypt(SAMPLE_ARABIC)
        best = brute_force_caesar(cipher_text, ARABIC)[0]
        self.assertEqual(best.key, 5)
        self.assertEqual(len(brute_force_caesar(cipher_text, ARABIC, top=3)), 3)

    def test_brute_force_affine(self):
        cipher_text = AffineCipher(7, 12).encrypt(SAMPLE_ENGLISH)
        results = brute_force_affine(cipher_text)
        self.assertEqual(results[0].key, (7, 12))
        self.assertEqual(len(results), 12 * 26)

    def test_attacks_reject_text_without_letters(self):
        with self.assertRaises(AnalysisError):
            brute_force_caesar("1234 !!!")
        with self.assertRaises(AnalysisError):
            brute_force_caesar("hello", ARABIC)

    def test_key_length_estimation(self):
        for key in ("LEMON", "CIPHER", "KEY", "SECRETS"):
            cipher_text = VigenereCipher(key).encrypt(SAMPLE_ENGLISH)
            estimates = estimate_key_length(cipher_text, max_len=15)
            self.assertEqual(estimates[0].length, len(key), key)
        self.assertEqual(estimate_key_length(CaesarCipher(4).encrypt(SAMPLE_ENGLISH))[0].length, 1)

    def test_kasiski_finds_multiples_of_key_length(self):
        cipher_text = VigenereCipher("CIPHER").encrypt(SAMPLE_ENGLISH)
        result = kasiski_examination(cipher_text)
        self.assertTrue(result.repeats)
        self.assertEqual(result.ranked_lengths(1)[0][0] % 3, 0)
        self.assertTrue(all(gap > 0 for gap in result.spacings))

    def test_break_vigenere(self):
        for key in ("LEMON", "CIPHER"):
            cipher_text = VigenereCipher(key).encrypt(SAMPLE_ENGLISH)
            best = break_vigenere(cipher_text)[0]
            self.assertEqual(best.key, key)
            self.assertEqual(best.plaintext, SAMPLE_ENGLISH)
        known = break_vigenere(VigenereCipher("KEY").encrypt(SAMPLE_ENGLISH), key_length=3)
        self.assertEqual(known[0].key, "KEY")

    def test_break_vigenere_reduces_repeated_key(self):
        cipher_text = VigenereCipher("ABABAB").encrypt(SAMPLE_ENGLISH)
        self.assertEqual(break_vigenere(cipher_text, key_length=6)[0].key, "AB")

    def test_xor_attacks(self):
        data = XorCipher.xor_bytes(SAMPLE_ENGLISH.encode(), b"\x5a" * len(SAMPLE_ENGLISH))
        best = brute_force_xor_single_byte(data)[0]
        self.assertEqual(best.key, b"\x5a")
        key = b"ICE"
        encrypted = XorCipher.xor_bytes(SAMPLE_ENGLISH.encode(), (key * 1000)[:len(SAMPLE_ENGLISH)])
        self.assertEqual(break_repeating_xor(encrypted)[0].key, key)
        self.assertEqual(hamming_distance(b"this is a test", b"wokka wokka!!!"), 37)

    def test_analysis_diagnosis(self):
        plain = analyze_text(SAMPLE_ENGLISH)
        self.assertIn("plaintext", plain.diagnosis)
        mono = analyze_text(CaesarCipher(9).encrypt(SAMPLE_ENGLISH))
        self.assertIn("monoalphabetic", mono.diagnosis)
        poly = analyze_text(VigenereCipher("CIPHERTEXTKEY").encrypt(SAMPLE_ENGLISH))
        self.assertTrue("polyalphabetic" in poly.diagnosis or "random" in poly.diagnosis)
        self.assertEqual(plain.frequencies[0][0], "E")
        with self.assertRaises(AnalysisError):
            analyze_text("12345")

    def test_custom_reference_profile(self):
        profile = FrequencyProfile.from_text(ENGLISH, SAMPLE_ENGLISH)
        best = brute_force_caesar(CaesarCipher(3).encrypt(SAMPLE_ENGLISH), ENGLISH, profile)[0]
        self.assertEqual(best.key, 3)
        with self.assertRaises(AnalysisError):
            FrequencyProfile.from_text(ENGLISH, "too short")

    def test_run_crack_dispatch(self):
        rows = run_crack("rot", CaesarCipher(8).encrypt(SAMPLE_ENGLISH), ENGLISH, top=2)
        self.assertEqual((len(rows), rows[0]["key"]), (2, "8"))
        hexed = XorCipher("k3y").encrypt(SAMPLE_ENGLISH)
        self.assertEqual(run_crack("xor", hexed, ENGLISH, {"format": "hex"}, top=1)[0]["key"][:6],
                         b"k3y".hex())
        with self.assertRaises(UnknownCipherError):
            run_crack("enigma", "text", ENGLISH)
        with self.assertRaises(InvalidKeyError):
            run_crack("caesar", "text", ENGLISH, {"bogus": 1})
        with self.assertRaises(InvalidInputError):
            run_crack("caesar", "   ", ENGLISH)


class TestRegistryAndFileIO(unittest.TestCase):
    def test_build_cipher_and_aliases(self):
        self.assertIsInstance(build_cipher("Vigenère", {"key": "k"}), VigenereCipher)
        self.assertIsInstance(build_cipher("ROT-N"), RotNCipher)
        self.assertIsInstance(build_cipher("transposition", {"key": "ab"}), ColumnarTranspositionCipher)
        with self.assertRaises(UnknownCipherError):
            build_cipher("rot47")
        with self.assertRaises(InvalidKeyError):
            build_cipher("caesar", {"shift": 3, "key": "x"})
        with self.assertRaises(InvalidKeyError):
            build_cipher("playfair", {"key": "abc"}, alphabet="arabic")

    def test_run_cipher_rejects_empty_text_and_bad_action(self):
        with self.assertRaises(InvalidInputError):
            run_cipher("encrypt", "caesar", "   ")
        with self.assertRaises(InvalidInputError):
            run_cipher("scramble", "caesar", "x")

    def test_text_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "nested" / "out.txt"
            write_text_file(path, "مرحبا\r\nworld")
            self.assertEqual(read_text_file(path), "مرحبا\nworld")
            bom = Path(tmp) / "bom.txt"
            bom.write_bytes(codecs.BOM_UTF8 + "hello".encode())
            self.assertEqual(read_text_file(bom), "hello")
            legacy = Path(tmp) / "win1256.txt"
            legacy.write_bytes("سلام".encode("cp1256"))
            self.assertEqual(read_text_file(legacy), "سلام")
            utf16 = Path(tmp) / "u16.txt"
            utf16.write_bytes("سلام".encode("utf-16"))
            self.assertEqual(read_text_file(utf16), "سلام")
            empty = Path(tmp) / "empty.txt"
            empty.write_bytes(b"  \n")
            with self.assertRaises(InvalidInputError):
                read_text_file(empty)
            with self.assertRaises(FileAccessError):
                read_text_file(Path(tmp) / "missing.txt")

    def test_resolve_text(self):
        self.assertEqual(resolve_text("a\r\nb", None), "a\nb")
        with self.assertRaises(InvalidInputError):
            resolve_text("   ", None)
        with self.assertRaises(InvalidInputError):
            resolve_text("x", "file.txt")
        with self.assertRaises(InvalidInputError):
            parse_kv_pairs(["novalue"])
        self.assertEqual(parse_kv_pairs(["a=1", "b=x=y"]), {"a": "1", "b": "x=y"})


class TestBatch(unittest.TestCase):
    def test_mixed_jobs_with_failures(self):
        jobs = [
            {"id": "enc", "action": "encrypt", "cipher": "caesar", "params": {"shift": 3}, "text": "abc"},
            {"id": "dec", "action": "decrypt", "cipher": "vigenere", "params": {"key": "LEMON"},
             "text": "LXFOPVEFRNHR"},
            {"id": "bad-key", "action": "encrypt", "cipher": "affine", "params": {"a": 2}, "text": "x"},
            {"id": "bad-action", "action": "explode", "text": "x"},
            {"id": "no-text", "action": "encrypt", "cipher": "caesar"},
            {"id": "crack", "action": "crack", "method": "caesar", "top": 1,
             "text": CaesarCipher(4).encrypt(SAMPLE_ENGLISH)},
            {"id": "analyze", "action": "analyze", "text": SAMPLE_ENGLISH},
            {"id": "keylen", "action": "keylen", "top": 2,
             "text": VigenereCipher("LEMON").encrypt(SAMPLE_ENGLISH)},
            {"id": "malformed", "action": "encrypt", "cipher": "caesar", "params": "oops", "text": "x"},
        ]
        results = {r.job_id: r for r in BatchProcessor().run(jobs)}
        self.assertEqual(results["enc"].output, "def")
        self.assertEqual(results["dec"].output, "ATTACKATDAWN")
        for failing in ("bad-key", "bad-action", "no-text", "malformed"):
            self.assertFalse(results[failing].ok, failing)
            self.assertTrue(results[failing].error)
        self.assertEqual(results["crack"].output[0]["key"], "4")
        self.assertEqual(results["keylen"].output[0]["length"], 5)
        self.assertIn("diagnosis", results["analyze"].output)

    def test_fail_fast_and_export(self):
        jobs = [{"action": "nope", "text": "x"}, {"action": "encrypt", "cipher": "caesar", "text": "x"}]
        self.assertEqual(len(BatchProcessor(fail_fast=True).run(jobs)), 1)
        results = BatchProcessor().run(jobs)
        payload = json.loads(export_results(results))
        self.assertEqual((payload["succeeded"], payload["failed"]), (1, 1))

    def test_file_jobs_defaults_and_relative_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            (base / "in.txt").write_text("مرحبا", encoding="utf-8")
            spec = {"defaults": {"alphabet": "arabic", "params": {"shift": 2}},
                    "jobs": [{"id": "f", "action": "encrypt", "cipher": "caesar",
                              "input_file": "in.txt", "output_file": "out/result.txt"}]}
            job_file = base / "jobs.json"
            job_file.write_text(json.dumps(spec, ensure_ascii=False), encoding="utf-8")
            jobs, folder = BatchProcessor.load_jobs(job_file)
            result = BatchProcessor(folder).run(jobs)[0]
            self.assertTrue(result.ok, result.error)
            self.assertEqual((base / "out" / "result.txt").read_text(encoding="utf-8"), result.output)
            self.assertEqual(result.output, CaesarCipher(2, ARABIC).encrypt("مرحبا"))

    def test_invalid_job_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = Path(tmp) / "bad.json"
            bad.write_text("{not json", encoding="utf-8")
            with self.assertRaises(BatchError):
                BatchProcessor.load_jobs(bad)
            for content in ("[]", '{"jobs": "x"}', '[1, 2]', '{"defaults": 5, "jobs": [{}]}'):
                bad.write_text(content, encoding="utf-8")
                with self.assertRaises(BatchError, msg=content):
                    BatchProcessor.load_jobs(bad)


class TestCLIAndMenu(unittest.TestCase):
    def test_encrypt_decrypt_round_trip(self):
        code, out, _ = _run_cli("encrypt", "caesar", "--shift", "-3", "--text", "Hello")
        self.assertEqual((code, out.strip()), (0, "Ebiil"))
        code, out, _ = _run_cli("decrypt", "caesar", "--shift=-3", "--text", "Ebiil")
        self.assertEqual(out.strip(), "Hello")
        code, out, _ = _run_cli("encrypt", "vigenere", "--key", "QUEENLY", "--mode", "autokey",
                                "--text", "ATTACKATDAWN")
        self.assertEqual(out.strip(), "QNXEPVYTWTWP")
        code, out, _ = _run_cli("encrypt", "caesar", "--alphabet", "arabic", "--shift", "1",
                                "--text", "ابت")
        self.assertEqual(out.strip(), "بتث")

    def test_errors_use_exit_code_two(self):
        for argv in (["encrypt", "affine", "--a", "2", "--text", "x"],
                     ["encrypt", "caesar", "--shift", "abc", "--text", "x"],
                     ["encrypt", "nonexistent", "--text", "x"],
                     ["encrypt", "caesar", "--text", "  "],
                     ["decrypt", "caesar", "--file", "/definitely/missing.txt"],
                     ["encrypt", "caesar", "--key", "x", "--text", "x"]):
            code, _, err = _run_cli(*argv)
            self.assertEqual(code, 2, argv)
            self.assertTrue(err.startswith("Error:"), argv)

    def test_file_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "x" / "c.txt"
            code, out, _ = _run_cli("encrypt", "rot", "--text", "Hello", "-o", str(target))
            self.assertEqual(code, 0)
            self.assertEqual(target.read_text(encoding="utf-8"), "Uryyb")
            self.assertIn("Saved", out)

    def test_crack_keylen_analyze_commands(self):
        cipher_text = CaesarCipher(6).encrypt(SAMPLE_ENGLISH)
        code, out, _ = _run_cli("crack", "caesar", "--text", cipher_text, "--top", "1", "--json")
        self.assertEqual(json.loads(out)[0]["key"], "6")
        vig = VigenereCipher("LEMON").encrypt(SAMPLE_ENGLISH)
        code, out, _ = _run_cli("keylen", "--text", vig, "--json", "--top", "1")
        self.assertEqual(json.loads(out)[0]["length"], 5)
        code, out, _ = _run_cli("crack", "vigenere", "--text", vig, "--top", "1")
        self.assertIn("key=LEMON", out)
        code, out, _ = _run_cli("analyze", "--text", SAMPLE_ENGLISH)
        self.assertIn("Diagnosis", out)

    def test_batch_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            job_file = Path(tmp) / "jobs.json"
            job_file.write_text(json.dumps([{"action": "encrypt", "cipher": "caesar", "text": "a"}]))
            code, out, _ = _run_cli("batch", str(job_file))
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(out)["results"][0]["output"], "d")
            job_file.write_text(json.dumps([{"action": "bogus", "text": "a"}]))
            self.assertEqual(_run_cli("batch", str(job_file))[0], 1)

    def test_list_and_demo(self):
        code, out, _ = _run_cli("list")
        for name in ("caesar", "affine", "vigenere", "playfair", "columnar", "xor", "enigma"):
            self.assertIn(name, out)
        code, out, _ = _run_cli("demo")
        self.assertEqual(code, 0)
        self.assertIn("true shift 11", out)

    def test_interactive_menu_scripted_session(self):
        script = iter([
            "1", "1", "1", "5", "1", "Hello World", "",    # encrypt: caesar, English, shift 5, typed text, no save
            "2", "1", "1", "5", "1", "Mjqqt Btwqi", "",    # decrypt the same way
            "x", "7", "0",                                 # invalid choice, list ciphers, exit
        ])
        shown: list[str] = []
        code = InteractiveMenu(read=lambda prompt: next(script), write=shown.append).run()
        joined = "\n".join(shown)
        self.assertEqual(code, 0)
        self.assertIn("Mjqqt Btwqi", joined)
        self.assertIn("Hello World", joined)
        self.assertIn("Invalid choice", joined)
        self.assertIn("Available ciphers", joined)

    def test_interactive_menu_reports_errors_and_handles_eof(self):
        answers = iter(["1", "3", "1", "2", "8", "1", "hello"])   # affine with the invalid a=2
        def reader(prompt: str) -> str:
            try:
                return next(answers)
            except StopIteration:
                raise EOFError from None
        shown: list[str] = []
        code = InteractiveMenu(read=reader, write=shown.append).run()
        self.assertEqual(code, 0)
        self.assertTrue(any("Error:" in line and "gcd(2, 26)" in line for line in shown))


# ----------------------------------------------------------------------------

if __name__ == "__main__":
    configure_console()
    sys.exit(main())
