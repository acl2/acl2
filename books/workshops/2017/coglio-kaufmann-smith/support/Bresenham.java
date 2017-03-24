class Bresenham {

    static void drawPoint (int x, int y) {
        // details unimportant
    }

    // draw a line from (0, 0) to (a, b), where 0 <= b <= a <= 1,000,000:
    static void drawLine(int a, int b) {
        int x = 0, y = 0, d = 2 * b - a;
        while (x <= a) {
            drawPoint(x, y);
            x++;
            if (d >= 0) {
                y++;
                d += 2 * (b - a);
            } else {
                d += 2 * b;
            }
        }
    }

}
