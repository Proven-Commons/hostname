// The Go oracle for tests/run_tests.py: crypto/x509's
// Certificate.VerifyHostname, with the presented identifier as the
// certificate's only DNS name.
//
// Each line of standard input is a reference identifier and a
// presented identifier, each as the hex digits of its bytes, joined
// by a space. Each line of output is 1 when VerifyHostname accepts,
// 0 when it does not, and error for a line it cannot read.
package main

import (
	"bufio"
	"crypto/x509"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"strings"
)

func answer(line string) string {
	parts := strings.Split(line, " ")
	if len(parts) != 2 {
		return "error"
	}
	r, err1 := hex.DecodeString(parts[0])
	p, err2 := hex.DecodeString(parts[1])
	if err1 != nil || err2 != nil {
		return "error"
	}
	cert := &x509.Certificate{DNSNames: []string{string(p)}}
	if cert.VerifyHostname(string(r)) == nil {
		return "1"
	}
	return "0"
}

func main() {
	in := bufio.NewReaderSize(os.Stdin, 1<<20)
	out := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	for {
		line, err := in.ReadString('\n')
		if len(line) > 0 {
			fmt.Fprintln(out, answer(strings.TrimRight(line, "\r\n")))
		}
		if err == io.EOF {
			return
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		// Answer each line before waiting for the next, so that a
		// caller may read each answer in turn.
		if in.Buffered() == 0 {
			out.Flush()
		}
	}
}
