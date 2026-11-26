# Cipher Machine & Cryptanalysis Suite

A self-contained Python 3.10+ toolkit (standard library only, zero external dependencies) for exploring classical ciphers, rotor machine mechanics, and statistical cryptanalysis.

> **Educational Use Only:** All ciphers in this project are historical or educational and can be broken. Do **not** use them to protect passwords or real-world sensitive data.

## Documentation
- **Full Manual:** See [`Cipher_Suite_Tool_Guide.pdf`](./Cipher_Suite_Tool_Guide.pdf) for detailed walkthroughs, diagrams, cipher rules, and troubleshooting.

## Key Features
- **Ciphers:** Caesar, ROT-N, Affine, Vigenère (Repeating & Autokey), Playfair, Columnar Transposition, XOR stream, and an Enigma-style rotor machine.
- **Cryptanalysis:** Brute-force attacks, Chi-squared ($\chi^2$), Index of Coincidence (IoC), Shannon entropy, Kasiski examination, Hamming distance key-length estimation, and automated breakers.
- **Alphabets:** English, Arabic, and custom alphabets (with file I/O support).
- **Modes:** Interactive menu, CLI sub-commands, file input/output (`--file` / `-o`), JSON batch jobs, and built-in `unittest` tests.

## Quick Start

```bash
# Run built-in unit tests
python cipher_suite.py test

# Run guided demo
python cipher_suite.py demo

# Open interactive menu
python cipher_suite.py

# Encrypt with Caesar cipher
python cipher_suite.py encrypt caesar --shift 3 --text "Hello, World!"

# Run sample JSON batch jobs
python cipher_suite.py batch sample_jobs.json -o results.json
