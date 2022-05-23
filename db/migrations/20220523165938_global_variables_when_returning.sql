-- migrate:up
CREATE TABLE `global_variables_when_returning` (
  `node_id` int unsigned,
  `global_variable_name` char(255) NOT NULL DEFAULT '',
  `global_variable_value` blob NOT NULL DEFAULT '',
  unique KEY (`node_id`, `global_variable_name`),
  CONSTRAINT `global_variables_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`),
  CONSTRAINT `global_variables_when_returning_fk_2` FOREIGN KEY (`node_id`, `global_variable_name`) REFERENCES `global_variables_on_entry` (`node_id`, `global_variable_name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE global_variables_when_returning;
