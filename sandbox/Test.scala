object Test {
  def fibonacci(n: Int): Int = {
    if (n < 2) {
      return n
    } else {
      return fibonacci(n-1) + fibonacci(n-2)
    }
  }

  def main(args: Array[String]): Unit = {
    val startTime = System.nanoTime()
    println(fibonacci(10))
    val endTime = System.nanoTime()
    val time = (endTime - startTime) / 1000
    println("Execution took " + time + " microseconds")
  }
}


