# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |

## Reporting a Vulnerability

If you discover a security vulnerability in idris2-echidna, please report it by:

1. **DO NOT** open a public GitHub issue
2. Email the maintainer at security@hyperpolymath.org
3. Include:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Suggested fix (if any)

We will acknowledge receipt within 48 hours and provide a detailed response within 7 days.

## Security Considerations

### Theorem Prover Integration

This library interfaces with external theorem provers (Z3, CVC5, Lean, etc.). When using these integrations:

- **Input Sanitization**: All formulas sent to provers should be validated
- **No Arbitrary Code Execution**: Proof results should not be used to execute arbitrary code
- **Process Isolation**: External prover processes should be properly sandboxed when possible

### FFI Security

The FFI layer (when implemented) will call native C libraries. Security considerations:

- Memory safety is ensured by Idris2's type system where possible
- Native library versions should be kept up to date
- Avoid passing user-controlled data directly to native functions without validation

## Security Updates

Security updates will be released as patch versions (e.g., 0.1.1) and announced via:

- GitHub Security Advisories
- Release notes

## Acknowledgments

We thank all security researchers who responsibly disclose vulnerabilities.
