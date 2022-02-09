import os

fn day_1(lines []string) {
	mut result := 0
	mut sliding_result := 0
	for i, line in lines {
		x := line.int()
		if i >= 1 && lines[i - 1].int() < x { result += 1 }
		if i >= 3 && lines[i - 3].int() < x { sliding_result += 1 }
	}
	println('Total increases: $result')
	println('Total increases with window size 3: $sliding_result')
}

fn day_2(lines []string) {
	mut depth := 0
	mut horiz := 0
	mut depth2 := 0
	for line in lines {
		parts := line.split(" ")
		cmd := parts[0]
		arg := parts[1].int()
		match cmd {
			"up" { depth -= arg }
			"down" { depth += arg }
			"forward" { horiz += arg
						depth2 += depth * arg }
			else {}
		}
	}
	println('Final depth * horiz: ${depth * horiz}')
	println('Final depth2 * horiz: ${depth2 * horiz}')
}

days := [day_1, day_2]
for i, day in days {
	println('== Day ${i+1} ==')
	day(os.read_lines('inputs/${i+1:02}.txt')?)
}
