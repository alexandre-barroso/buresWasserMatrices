# Public input and fixed analysis protocol

The input is the public Hillenbrand et al. (1995) archive mirrored by Santiago Barreda with the README's explicit statement that it is hosted with Jim Hillenbrand's permission. That provenance does not require redistribution of the archive by this project: no raw measurement files, recordings or archive members are included here.

- Mirror: https://github.com/santiagobarreda/hillenbrand_et_al_1995
- Fixed commit: `6dd44decc8ef5b537cbb54732a3b00c8fa652e65`
- Exact file: https://raw.githubusercontent.com/santiagobarreda/hillenbrand_et_al_1995/6dd44decc8ef5b537cbb54732a3b00c8fa652e65/h95-alldata.zip
- Archive size: 21,748,822 bytes.
- Archive SHA256: `2560548591e3a726c88549b6dc9d226995616c26874d601c69fee8b9eee9d730`.
- Read member: `vowdata.dat`; SHA256 `05a4a69e2c6b0f444077245b1427d12bc86f8d7a32ae7a4b63f7e06e5712e4b1`.

Obtain the ZIP separately and keep it outside the repository. Do not unpack its nested audio archives for this analysis. The code reads only ASCII numeric text in `vowdata.dat`; it executes no archive content and does not deserialize the mirror's R objects. A wrong archive hash is an error.

The archive contains 1,668 speaker-by-category records: 139 speakers and 12 categories each. Published group labels are retained (45 men, 48 women, 46 children). The analysis uses the manually selected steady-state F1/F2 columns, treating zero as unmeasurable. These are not automatically fixed midpoint measurements.

The primary `raw_hz` representation retains paired-complete F1/F2 records separately per category: 1,658 records, with group totals 540, 574 and 544. Both means and the two-dimensional covariance use the same paired records. The script does not use the article's identification-filtered descriptive table or substitute marginal sample sizes for paired sample sizes.

`raw_complete` keeps complete 12-category panels (45 men, 46 women, 39 children; 1,560 records). `lobanov_complete` uses these same panels and divides each speaker's centered formant coordinates by its RMS over all 12 categories, denominator 12. This matched raw analysis separates panel selection from transformation. Group category covariances use denominator n−1 in all representations. No normalization is fitted to target-group summaries alone.

All 12 references and every unordered pair of the remaining 11 targets are evaluated: 660 strict-order questions per group. All nearest-category candidates are retained. Every one-speaker omission is recomputed in the appropriate selected group (139 +130 +130 =399). These deterministic sensitivity runs are not independent replications or confidence intervals. Original public speaker codes in omission outputs identify which record block was left out; no individual source measurements are exported.

The retained-covariance comparator is a Gaussian model defined by finite-sample means/covariances. The diagonal Gaussian distance equals the exact lower endpoint. The loose upper bound is mean separation plus covariance trace; it is a mathematical comparator, not asserted to be a customary phonetic method. Fixed coordinates and units are part of the question: scaling changes the estimand.

The normalization preserves cross-category row identities that the unrestricted completion theorem does not impose. Therefore certified inequalities remain safe for any compatible normalized dataset, but an ambiguous unrestricted interval does not establish that every endpoint is attainable by a dataset preserving all normalization identities. Likewise, the theorem's constructed common reference usually differs from the observed reference covariance.

Bibliographic data for the actual locally read editions supporting the measurement and normalization choices:

- James Hillenbrand, Laura A. Getty, Michael J. Clark and Kimberlee Wheeler (1995). Acoustic characteristics of American English vowels. *Journal of the Acoustical Society of America* 97(5), 3099–3111. DOI: https://doi.org/10.1121/1.411872 . The article is distinct from the 1994 conference abstract associated with DOI 10.1121/1.409456.
- B. M. Lobanov (1971). Classification of Russian Vowels Spoken by Different Speakers. *Journal of the Acoustical Society of America* 49(2B), 606–608. DOI: https://doi.org/10.1121/1.1912396 . Equation 2 and the accompanying RMS description motivate the specified speaker normalization; they do not validate a universal acoustic distance.

These references are bibliographic provenance only; their full texts are not redistributed in this repository.
