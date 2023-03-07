def main():
    from sys import stdin
    lines = [line.lstrip().rstrip() for line in stdin][2:-1]
    houses = {}
    for i in range(0, len(lines), 2):
        start = lines[i].find("fun") + 4
        end = lines[i][start:].find(" ")
        var = lines[i][start:start + end + 1]
        category, value = var.split("-")
        house_number = lines[i+1][:-1]
        if house_number in houses:
            houses[house_number][category] = value
        else:
            houses[house_number] = {category:value}
    
    print("{:<1} {:<10} {:<10} {:<10} {:<10} {:<10}".format('#', 'color', 'resident', 'pet', 'drink', 'language'))
    print("{:<1} {:<10} {:<10} {:<10} {:<10} {:<10}".format('-', '----------', '----------', '----------', '----------', '----------'))

    for k in sorted(houses.keys()):
        v = houses[k]
        print("{:<1} {:<10} {:<10} {:<10} {:<10} {:<10}".format(k, v['color'], v['person'], v['pet'], v['drink'], v['lang']))

if __name__ == "__main__":
    main()
