-- migrate:up
CREATE TABLE `arguments_when_returning` (
  `node_id` int unsigned,
  `argument_name` char(255) NOT NULL DEFAULT '',
  `argument_value` blob NOT NULL DEFAULT '',
  unique KEY (`node_id`, `argument_name`),
  CONSTRAINT `arguments_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`),
  CONSTRAINT `arguments_when_returning_fk_2` FOREIGN KEY (`node_id`, `argument_name`) REFERENCES `arguments_on_entry` (`node_id`, `argument_name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE arguments_when_returning;
