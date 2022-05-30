-- migrate:up
CREATE TABLE `benchmarks` (
  `my_vector_length` int unsigned,
  `number_of_nodes` int unsigned,
  `building_time_ns` bigint unsigned
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down

DROP TABLE benchmarks;
