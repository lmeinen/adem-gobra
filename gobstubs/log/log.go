// +gobra
package log

// These functions write to the standard logger.

// Print calls Output to print to the standard logger.
func Print(v ...any)

// Printf calls Output to print to the standard logger.
func Printf(format string, v ...any)

// Println calls Output to print to the standard logger.
func Println(v ...any)
