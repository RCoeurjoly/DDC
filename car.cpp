int number_of_cars = 0;

class Car {
public:
  Car() {
    x = 0;
    y = 0;
    number_of_cars++;
  };
  bool move(const int& xDelta, const int& yDelta) {
    x += xDelta;
    y += yDelta;
    return true;
  };
private:
  int x;
  int y;
};

int main() {
  Car my_car;
  my_car.move(10, 5);
}
